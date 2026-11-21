use crate::config::{
    log_debug, log_info, log_warn, now_monotonic, PROFILED_APPDATA_LEN, STATS,
    TLS_APPDATA_MAX, TLS_APPDATA_MIN, TLS_CIPHER_PREFERENCE,
    TLS_FALLBACK_APPDATA_MAX, TLS_FALLBACK_APPDATA_MIN, TLS_GROUP_X25519,
    TLS_GROUP_X25519MLKEM768, TLS_MLKEM768_CIPHERTEXT_LEN, TLS_PROFILE_PROBE_TIMEOUT,
    TLS_REPLAY_CACHE_SIZE, TLS_REPLAY_WINDOW, TLS_SERVER_HELLO_DELAY_MS,
    TLS_X25519MLKEM768_CLIENT_SHARE_LEN,
};
use hmac::{Hmac, Mac};
use once_cell::sync::Lazy;
use parking_lot::Mutex;
use rand::RngCore;
use sha2::Sha256;
use std::collections::{HashMap, HashSet, VecDeque};
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt, ReadHalf, WriteHalf};
use tokio::net::TcpStream;
use tokio::time::Instant;

pub const TLS_RECORD_HANDSHAKE: u8 = 0x16;
pub const TLS_RECORD_CCS: u8 = 0x14;
pub const TLS_RECORD_APPDATA: u8 = 0x17;

const CLIENT_RANDOM_OFFSET: usize = 11;
const CLIENT_RANDOM_LEN: usize = 32;
const SESSION_ID_OFFSET: usize = 44;
const SESSION_ID_LEN: usize = 32;

const TIMESTAMP_TOLERANCE: i64 = 120;

const READ_HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(10);
const READ_RECORD_TIMEOUT: Duration = Duration::from_secs(10);
const MASKING_CONNECT_TIMEOUT: Duration = Duration::from_secs(10);

const CCS_FRAME: [u8; 6] = [0x14, 0x03, 0x03, 0x00, 0x01, 0x01];

const SH_RANDOM_OFF: usize = 11;

const EXT_SUPPORTED_VERSIONS: u16 = 0x002b;
const EXT_KEY_SHARE: u16 = 0x0033;

type HmacSha256 = Hmac<Sha256>;

pub struct FakeTlsStream {
    pub read: Box<dyn AsyncRead + Send + Unpin>,
    pub write: Box<dyn AsyncWrite + Send + Unpin>,
}

/// proxy/fake_tls.py::ClientHelloInfo — предлагаемые шифры и key_share.
#[derive(Default)]
struct ClientHelloInfo {
    cipher_suites: HashSet<u16>,
    key_shares: HashMap<u16, usize>,
}

/// proxy/fake_tls.py::_ReplayCache — успешно проверенные ClientRandom'ы.
/// Кэш Lives lifetime процесса: переживает перезапуск прокси.
struct ReplayCache {
    expiry: VecDeque<([u8; 32], f64)>,
    seen: HashMap<[u8; 32], f64>,
}

impl ReplayCache {
    fn new() -> Self {
        ReplayCache {
            expiry: VecDeque::new(),
            seen: HashMap::new(),
        }
    }

    fn first_seen(&mut self, client_random: &[u8; 32]) -> bool {
        let now = now_monotonic();
        while let Some((_, until)) = self.expiry.front() {
            if *until > now {
                break;
            }
            if let Some(old) = self.expiry.pop_front() {
                self.seen.remove(&old.0);
            }
        }
        if self.seen.contains_key(client_random) {
            return false;
        }
        if self.seen.len() >= TLS_REPLAY_CACHE_SIZE {
            if let Some(old) = self.expiry.pop_front() {
                self.seen.remove(&old.0);
            }
        }
        let until = now + TLS_REPLAY_WINDOW;
        self.expiry.push_back((*client_random, until));
        self.seen.insert(*client_random, until);
        true
    }
}

static REPLAY_CACHE: Lazy<Mutex<ReplayCache>> = Lazy::new(|| Mutex::new(ReplayCache::new()));

fn parse_client_hello(data: &[u8]) -> ClientHelloInfo {
    let mut info = ClientHelloInfo::default();
    let mut pos = 5usize + 4 + 2 + CLIENT_RANDOM_LEN;
    let session_len = match data.get(pos) {
        Some(v) => *v as usize,
        None => return info,
    };
    pos = match pos.checked_add(1 + session_len) {
        Some(p) => p,
        None => return info,
    };
    let suites_len = match read_u16(data, pos) {
        Some(v) => v as usize,
        None => return info,
    };
    pos += 2;
    let suites_end = match pos.checked_add(suites_len) {
        Some(v) if v <= data.len() => v,
        _ => return info,
    };
    let mut off = pos;
    while off + 2 <= suites_end {
        if let Some(suite) = read_u16(data, off) {
            info.cipher_suites.insert(suite);
        }
        off += 2;
    }
    pos = suites_end;
    let compression_len = match data.get(pos) {
        Some(v) => *v as usize,
        None => return info,
    };
    pos = match pos.checked_add(1 + compression_len) {
        Some(p) => p,
        None => return info,
    };
    let ext_total = match read_u16(data, pos) {
        Some(v) => v as usize,
        None => return info,
    };
    pos += 2;
    let ext_end = pos.saturating_add(ext_total).min(data.len());
    while pos + 4 <= ext_end {
        let ext_type = match read_u16(data, pos) {
            Some(v) => v,
            None => break,
        };
        let ext_len = match read_u16(data, pos + 2) {
            Some(v) => v as usize,
            None => break,
        };
        pos += 4;
        if ext_type == EXT_KEY_SHARE && pos + 2 <= ext_end {
            let shares_len = read_u16(data, pos).unwrap_or(0) as usize;
            let shares_end = pos.saturating_add(2 + shares_len).min(ext_end);
            let mut s = pos + 2;
            while s + 4 <= shares_end {
                let group = read_u16(data, s).unwrap_or(0);
                let key_len = read_u16(data, s + 2).unwrap_or(0) as usize;
                let next = s.saturating_add(4 + key_len);
                if next > shares_end {
                    break;
                }
                info.key_shares.entry(group).or_insert(key_len);
                s = next;
            }
        }
        pos = match pos.checked_add(ext_len) {
            Some(p) if p <= ext_end => p,
            _ => break,
        };
    }
    info
}

fn read_u16(data: &[u8], pos: usize) -> Option<u16> {
    let bytes = data.get(pos..pos.checked_add(2)?)?;
    Some(u16::from_be_bytes([bytes[0], bytes[1]]))
}

fn select_cipher_suite(info: &ClientHelloInfo) -> u16 {
    TLS_CIPHER_PREFERENCE
        .iter()
        .copied()
        .find(|suite| info.cipher_suites.contains(suite))
        .unwrap_or(TLS_CIPHER_PREFERENCE[0])
}

fn x25519_public_key() -> [u8; 32] {
    let mut key = [0u8; 32];
    rand::thread_rng().fill_bytes(&mut key);
    key[31] &= 0x7f;
    key
}

fn server_key_share(info: &ClientHelloInfo) -> (u16, Vec<u8>) {
    if info.key_shares.get(&TLS_GROUP_X25519MLKEM768) == Some(&TLS_X25519MLKEM768_CLIENT_SHARE_LEN)
    {
        let mut share = vec![0u8; TLS_MLKEM768_CIPHERTEXT_LEN + 32];
        rand::thread_rng().fill_bytes(&mut share[..TLS_MLKEM768_CIPHERTEXT_LEN]);
        share[TLS_MLKEM768_CIPHERTEXT_LEN..].copy_from_slice(&x25519_public_key());
        (TLS_GROUP_X25519MLKEM768, share)
    } else {
        (TLS_GROUP_X25519, x25519_public_key().to_vec())
    }
}

fn appdata_len() -> usize {
    if let Some(len) = *PROFILED_APPDATA_LEN.read() {
        return len.clamp(TLS_APPDATA_MIN, TLS_APPDATA_MAX);
    }
    let mut rng = rand::thread_rng();
    TLS_FALLBACK_APPDATA_MIN + (rng.next_u32() as usize) % (TLS_FALLBACK_APPDATA_MAX - TLS_FALLBACK_APPDATA_MIN + 1)
}

fn verify_client_hello(data: &[u8], secret: &[u8]) -> Option<([u8; 32], [u8; 32], i64)> {
    if data.len() < 43 {
        return None;
    }
    if data[0] != TLS_RECORD_HANDSHAKE {
        return None;
    }
    if data[5] != 0x01 {
        return None;
    }

    let mut client_random = [0u8; 32];
    client_random
        .copy_from_slice(&data[CLIENT_RANDOM_OFFSET..CLIENT_RANDOM_OFFSET + CLIENT_RANDOM_LEN]);

    let mut zeroed = data.to_vec();
    for b in &mut zeroed[CLIENT_RANDOM_OFFSET..CLIENT_RANDOM_OFFSET + CLIENT_RANDOM_LEN] {
        *b = 0;
    }

    let mut mac = HmacSha256::new_from_slice(secret).ok()?;
    mac.update(&zeroed);
    let expected = mac.finalize().into_bytes();

    if expected[..28] != client_random[..28] {
        return None;
    }

    let mut ts_bytes = [0u8; 4];
    for i in 0..4 {
        ts_bytes[i] = client_random[28 + i] ^ expected[28 + i];
    }
    let timestamp = u32::from_le_bytes(ts_bytes) as i64;

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    if (now - timestamp).abs() > TIMESTAMP_TOLERANCE {
        return None;
    }

    let mut session_id = [0u8; 32];
    if data.len() >= SESSION_ID_OFFSET + SESSION_ID_LEN && data[43] == 0x20 {
        session_id
            .copy_from_slice(&data[SESSION_ID_OFFSET..SESSION_ID_OFFSET + SESSION_ID_LEN]);
    }

    Some((client_random, session_id, timestamp))
}

fn build_server_hello(
    secret: &[u8],
    client_random: &[u8; 32],
    session_id: &[u8; 32],
    info: &ClientHelloInfo,
) -> Vec<u8> {
    let (group, key_exchange) = server_key_share(info);

    let mut extensions = Vec::with_capacity(12 + key_exchange.len());
    extensions.extend_from_slice(&EXT_SUPPORTED_VERSIONS.to_be_bytes());
    extensions.extend_from_slice(&2u16.to_be_bytes());
    extensions.extend_from_slice(&0x0304u16.to_be_bytes());
    extensions.extend_from_slice(&EXT_KEY_SHARE.to_be_bytes());
    extensions.extend_from_slice(&((4 + key_exchange.len()) as u16).to_be_bytes());
    extensions.extend_from_slice(&group.to_be_bytes());
    extensions.extend_from_slice(&(key_exchange.len() as u16).to_be_bytes());
    extensions.extend_from_slice(&key_exchange);

    let mut body = Vec::with_capacity(2 + 32 + 1 + 32 + 2 + 1 + 2 + extensions.len());
    body.extend_from_slice(&[0x03, 0x03]);
    body.extend_from_slice(&[0u8; 32]);
    body.push(32);
    body.extend_from_slice(session_id);
    body.extend_from_slice(&select_cipher_suite(info).to_be_bytes());
    body.push(0);
    body.extend_from_slice(&(extensions.len() as u16).to_be_bytes());
    body.extend_from_slice(&extensions);

    let mut message = Vec::with_capacity(4 + body.len());
    message.push(0x02);
    message.extend_from_slice(&(body.len() as u32).to_be_bytes()[1..]);
    message.extend_from_slice(&body);

    let mut response = Vec::with_capacity(5 + message.len() + CCS_FRAME.len() + 5 + TLS_APPDATA_MAX);
    response.push(TLS_RECORD_HANDSHAKE);
    response.extend_from_slice(&[0x03, 0x03]);
    response.extend_from_slice(&(message.len() as u16).to_be_bytes());
    response.extend_from_slice(&message);
    response.extend_from_slice(&CCS_FRAME);

    let size = appdata_len();
    let mut encrypted_data = vec![0u8; size];
    rand::thread_rng().fill_bytes(&mut encrypted_data);
    response.push(TLS_RECORD_APPDATA);
    response.extend_from_slice(&[0x03, 0x03]);
    response.extend_from_slice(&(size as u16).to_be_bytes());
    response.extend_from_slice(&encrypted_data);

    let mut mac = HmacSha256::new_from_slice(secret).unwrap();
    mac.update(client_random);
    mac.update(&response);
    let server_random = mac.finalize().into_bytes();
    response[SH_RANDOM_OFF..SH_RANDOM_OFF + 32].copy_from_slice(&server_random);
    response
}

/// Длина первого ApplicationData record'а в первом flight'е сервера.
/// None — данных пока мало, Some(0) — record'а нет (alert / TLS 1.2).
fn first_appdata_record_len(data: &[u8]) -> Option<usize> {
    let mut pos = 0usize;
    while pos + 5 <= data.len() {
        let rtype = data[pos];
        let rec_len = u16::from_be_bytes([data[pos + 3], data[pos + 4]]) as usize;
        if rtype == TLS_RECORD_APPDATA {
            return Some(rec_len);
        }
        if rtype != TLS_RECORD_HANDSHAKE && rtype != TLS_RECORD_CCS {
            return Some(0);
        }
        pos = match pos.checked_add(5 + rec_len) {
            Some(p) => p,
            None => return Some(0),
        };
    }
    None
}

/// Генерирует TLS 1.3 ClientHello через rustls (без завершения handshake).
fn probe_client_hello(domain: &str) -> Option<Vec<u8>> {
    use rustls::{ClientConfig, ClientConnection, RootCertStore};

    let mut cfg = ClientConfig::builder()
        .with_root_certificates(RootCertStore::empty())
        .with_no_client_auth();
    cfg.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
    let name = rustls::pki_types::ServerName::try_from(domain.to_string()).ok()?;
    let mut conn = ClientConnection::new(Arc::new(cfg), name).ok()?;
    let mut outgoing = Vec::new();
    conn.write_tls(&mut outgoing).ok()?;
    if outgoing.is_empty() {
        None
    } else {
        Some(outgoing)
    }
}

/// proxy/fake_tls.py::probe_appdata_len — замер первого зашифрованного
/// record'а маскирующего сайта. Один общий дедлайн на все фазы.
pub async fn probe_appdata_len(domain: &str) -> Option<usize> {
    let client_hello = probe_client_hello(domain)?;
    let deadline = Instant::now() + TLS_PROFILE_PROBE_TIMEOUT;
    let mut stream = tokio::time::timeout_at(
        deadline,
        TcpStream::connect(format!("{}:443", domain)),
    )
    .await
    .ok()?
    .ok()?;

    tokio::time::timeout_at(deadline, stream.write_all(&client_hello))
        .await
        .ok()?
        .ok()?;

    let mut buf = [0u8; 16384];
    let mut flight = Vec::new();
    loop {
        if Instant::now() >= deadline {
            return None;
        }
        let n = tokio::time::timeout_at(deadline, stream.read(&mut buf))
            .await
            .ok()?
            .ok()?;
        if n == 0 {
            return None;
        }
        flight.extend_from_slice(&buf[..n]);
        match first_appdata_record_len(&flight) {
            Some(0) => return None,
            Some(len) => return Some(len),
            None => continue,
        }
    }
}

pub async fn run_profile_probe(domain: String) {
    *PROFILED_APPDATA_LEN.write() = None;
    match probe_appdata_len(&domain).await {
        Some(len) => {
            let clamped = len.clamp(TLS_APPDATA_MIN, TLS_APPDATA_MAX);
            *PROFILED_APPDATA_LEN.write() = Some(clamped);
            log_info(&format!(
                "Fake TLS profile: first encrypted record {} bytes",
                clamped
            ));
        }
        None => {
            *PROFILED_APPDATA_LEN.write() = None;
            log_warn("Fake TLS profile unavailable, ServerHello uses random record sizes");
        }
    }
}

fn wrap_tls_record(data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(data.len() + 5 * (data.len() / TLS_APPDATA_MAX + 1));
    let mut offset = 0;
    while offset < data.len() {
        let end = std::cmp::min(offset + TLS_APPDATA_MAX, data.len());
        let chunk = &data[offset..end];
        out.push(TLS_RECORD_APPDATA);
        out.push(0x03);
        out.push(0x03);
        out.push((chunk.len() >> 8) as u8);
        out.push(chunk.len() as u8);
        out.extend_from_slice(chunk);
        offset = end;
    }
    out
}

struct TlsRecordReader {
    inner: ReadHalf<TcpStream>,
    buf: Vec<u8>,
    pos: usize,
    read_left: usize,
}

impl TlsRecordReader {
    fn new(inner: ReadHalf<TcpStream>) -> Self {
        TlsRecordReader {
            inner,
            buf: Vec::new(),
            pos: 0,
            read_left: 0,
        }
    }

    fn compact(&mut self) {
        if self.pos > 0 {
            self.buf.drain(..self.pos);
            self.pos = 0;
        }
    }

    fn next_payload(
        &mut self,
    ) -> Pin<Box<dyn Future<Output = std::io::Result<Vec<u8>>> + Send + '_>> {
        Box::pin(async move {
            loop {
                if self.read_left > 0 {
                    let want = std::cmp::min(self.read_left, 16384);
                    let mut chunk = vec![0u8; want];
                    let n = self.inner.read(&mut chunk).await?;
                    if n == 0 {
                        return Ok(Vec::new());
                    }
                    chunk.truncate(n);
                    self.read_left -= n;
                    return Ok(chunk);
                }

                let mut hdr = [0u8; 5];
                self.inner.read_exact(&mut hdr).await?;
                let rtype = hdr[0];
                let rec_len = u16::from_be_bytes([hdr[3], hdr[4]]) as usize;

                if rtype == TLS_RECORD_CCS {
                    if rec_len > 0 {
                        let mut junk = vec![0u8; rec_len];
                        self.inner.read_exact(&mut junk).await?;
                    }
                    continue;
                }

                if rtype != TLS_RECORD_APPDATA {
                    return Ok(Vec::new());
                }

                let want = std::cmp::min(rec_len, 65536);
                let mut chunk = vec![0u8; want];
                let n = self.inner.read(&mut chunk).await?;
                if n == 0 {
                    return Ok(Vec::new());
                }
                chunk.truncate(n);
                if rec_len > n {
                    self.read_left = rec_len - n;
                }
                return Ok(chunk);
            }
        })
    }
}

impl AsyncRead for TlsRecordReader {
    fn poll_read(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
        buf: &mut tokio::io::ReadBuf<'_>,
    ) -> std::task::Poll<std::io::Result<()>> {
        let this = self.get_mut();

        loop {
            let avail = this.buf.len() - this.pos;
            if avail > 0 {
                let n = std::cmp::min(avail, buf.remaining());
                let src = &this.buf[this.pos..this.pos + n];
                buf.put_slice(src);
                this.pos += n;
                if this.pos == this.buf.len() {
                    this.buf.clear();
                    this.pos = 0;
                }
                return std::task::Poll::Ready(Ok(()));
            }

            this.compact();
            let polled = {
                let mut fut = this.next_payload();
                Pin::new(&mut fut).poll(cx)
            };
            match polled {
                std::task::Poll::Pending => return std::task::Poll::Pending,
                std::task::Poll::Ready(Err(e)) => {
                    return std::task::Poll::Ready(Err(
                        if e.kind() == std::io::ErrorKind::UnexpectedEof {
                            std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "faketls eof")
                        } else {
                            e
                        },
                    ))
                }
                std::task::Poll::Ready(Ok(payload)) => {
                    if payload.is_empty() {
                        return std::task::Poll::Ready(Ok(()));
                    }
                    this.buf = payload;
                    this.pos = 0;
                }
            }
        }
    }
}

struct TlsRecordWriter {
    inner: WriteHalf<TcpStream>,
}

impl TlsRecordWriter {
    fn new(inner: WriteHalf<TcpStream>) -> Self {
        TlsRecordWriter { inner }
    }
}

impl AsyncWrite for TlsRecordWriter {
    fn poll_write(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
        buf: &[u8],
    ) -> std::task::Poll<std::io::Result<usize>> {
        let this = self.get_mut();
        let wrapped = wrap_tls_record(buf);
        match Pin::new(&mut this.inner).poll_write(cx, &wrapped) {
            std::task::Poll::Pending => std::task::Poll::Pending,
            std::task::Poll::Ready(Ok(n)) => {
                std::task::Poll::Ready(Ok(if n >= buf.len() { buf.len() } else { n }))
            }
            std::task::Poll::Ready(Err(e)) => std::task::Poll::Ready(Err(e)),
        }
    }

    fn poll_flush(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<std::io::Result<()>> {
        Pin::new(&mut self.get_mut().inner).poll_flush(cx)
    }

    fn poll_shutdown(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<std::io::Result<()>> {
        Pin::new(&mut self.get_mut().inner).poll_shutdown(cx)
    }
}

pub async fn server_handshake(
    mut conn: TcpStream,
    first: u8,
    secret: &[u8],
    masking: &str,
    label: &str,
) -> Option<FakeTlsStream> {
    let mut hdr_rest = [0u8; 4];
    match tokio::time::timeout(READ_HANDSHAKE_TIMEOUT, conn.read_exact(&mut hdr_rest)).await {
        Ok(Ok(_)) => {}
        _ => {
            log_debug(&format!("[{}] incomplete TLS record header", label));
            return None;
        }
    }

    let mut tls_header = [0u8; 5];
    tls_header[0] = first;
    tls_header[1..5].copy_from_slice(&hdr_rest);
    let record_len = u16::from_be_bytes([tls_header[3], tls_header[4]]) as usize;

    let mut body = vec![0u8; record_len];
    match tokio::time::timeout(READ_RECORD_TIMEOUT, conn.read_exact(&mut body)).await {
        Ok(Ok(_)) => {}
        _ => {
            log_debug(&format!("[{}] incomplete TLS record body", label));
            return None;
        }
    }

    let mut client_hello = Vec::with_capacity(5 + record_len);
    client_hello.extend_from_slice(&tls_header);
    client_hello.extend_from_slice(&body);

    let tls_result = verify_client_hello(&client_hello, secret);
    let replayed = tls_result
        .as_ref()
        .map(|(random, _, _)| !REPLAY_CACHE.lock().first_seen(random))
        .unwrap_or(false);

    if tls_result.is_none() || replayed {
        log_debug(&format!(
            "[{}] Fake TLS {} (size={} rec={}) -> masking",
            label,
            if replayed { "hello replayed" } else { "verify failed" },
            client_hello.len(),
            record_len
        ));
        proxy_to_masking_domain(conn, client_hello, masking, label).await;
        return None;
    }

    let (client_random, session_id, ts) = tls_result.unwrap();
    log_debug(&format!("[{}] Fake TLS handshake ok (ts={})", label, ts));

    let hello_info = parse_client_hello(&client_hello);
    let server_hello = build_server_hello(secret, &client_random, &session_id, &hello_info);

    let (delay_lo, delay_hi) = TLS_SERVER_HELLO_DELAY_MS;
    let delay_ms = delay_lo + rand::thread_rng().next_u64() % (delay_hi - delay_lo + 1);
    tokio::time::sleep(Duration::from_millis(delay_ms)).await;

    if conn.write_all(&server_hello).await.is_err() {
        return None;
    }
    let _ = conn.flush().await;

    let (r, w) = tokio::io::split(conn);
    Some(FakeTlsStream {
        read: Box::new(TlsRecordReader::new(r)),
        write: Box::new(TlsRecordWriter::new(w)),
    })
}

async fn proxy_to_masking_domain(conn: TcpStream, initial: Vec<u8>, domain: &str, label: &str) {
    let upstream = match tokio::time::timeout(
        MASKING_CONNECT_TIMEOUT,
        TcpStream::connect((domain, 443u16)),
    )
    .await
    {
        Ok(Ok(s)) => s,
        _ => {
            log_warn(&format!(
                "[{}] masking: cannot connect to {}:443",
                label, domain
            ));
            return;
        }
    };

    log_debug(&format!("[{}] masking -> {}:443", label, domain));
    STATS
        .connections_masked
        .fetch_add(1, Ordering::Relaxed);

    let mut upstream = upstream;
    if upstream.write_all(&initial).await.is_err() {
        return;
    }

    let (mut c_read, mut c_write) = tokio::io::split(conn);
    let (mut u_read, mut u_write) = tokio::io::split(upstream);

    let up = tokio::spawn(async move {
        let _ = tokio::io::copy(&mut c_read, &mut u_write).await;
        let _ = u_write.shutdown().await;
    });
    let down = tokio::spawn(async move {
        let _ = tokio::io::copy(&mut u_read, &mut c_write).await;
        let _ = c_write.shutdown().await;
    });

    let _ = tokio::join!(up, down);
}
