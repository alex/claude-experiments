//! The DNS stub resolver behind `getaddrinfo`, `getnameinfo` and the
//! `gethostby*` family.
//!
//! Configuration comes from `/etc/resolv.conf` (`nameserver`, `search`,
//! `domain`, `options ndots:/timeout:/attempts:`), read on every lookup
//! so that changes take effect without a restart. As an extension a
//! nameserver may carry a port (`10.0.0.1:5353`, `[::1]:5353`). Each lookup sends the
//! query for every wanted record type to every nameserver at once over
//! UDP and takes the first valid answer per type, retrying after the
//! timeout; a truncated reply is re-asked over TCP.
//!
//! Replies are accepted only if they come from a configured server, carry
//! the ID of an outstanding query and echo its question. Answer records
//! count only when their owner is the queried name or the target of a
//! CNAME chain that starts at it; other records (glue, additional
//! sections) are ignored. Name decompression bounds the pointer chase, so
//! a malicious server cannot loop or read outside the message.

use crate::errno::Errno;
use crate::poll::PollFd;
use crate::socket::{AF_INET, AF_INET6, Addr, SOCK_DGRAM, SOCK_STREAM, SockaddrIn, SockaddrIn6};
use crate::sys::{self, Timespec};

const POLLIN: i16 = 1;
const POLLOUT: i16 = 4;
const SOCK_CLOEXEC: c_int = 0o2000000;
const SOCK_NONBLOCK: c_int = 0o4000;
use core::ffi::{c_char, c_int, c_void};
use core::ptr;
use core::sync::atomic::{AtomicPtr, Ordering};

/// Why a lookup produced no addresses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The name does not exist (or has no records of the wanted types).
    NoName,
    /// No usable answer in time; may succeed later.
    Again,
    /// The name is malformed or the server's reply was.
    Fail,
}

const TYPE_A: u16 = 1;
const TYPE_CNAME: u16 = 5;
const TYPE_PTR: u16 = 12;
const TYPE_AAAA: u16 = 28;
const CLASS_IN: u16 = 1;
const MAX_SERVERS: usize = 3;
const MAX_SEARCH: usize = 6;
const MAX_NAME: usize = 253;
/// Largest UDP reply we accept (RFC 1035 size).
const UDP_MAX: usize = 512;

/// A configured nameserver.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Server {
    addr: Addr,
    port: u16,
}

struct Config {
    servers: [Option<Server>; MAX_SERVERS],
    search: [([u8; MAX_NAME + 1], usize); MAX_SEARCH],
    nsearch: usize,
    ndots: u32,
    /// Per-attempt timeout in milliseconds.
    timeout_ms: u32,
    attempts: u32,
}

/// Path of the configuration file; a test hook can point it elsewhere.
static CONF_PATH: AtomicPtr<c_char> = AtomicPtr::new(ptr::null_mut());

/// Test hook: reads resolver configuration from `path` (which must stay
/// valid) instead of `/etc/resolv.conf`.
///
/// # Safety
/// `path` must be NUL-terminated and live for the rest of the process.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __rustlibc_set_resolv_conf(path: *const c_char) {
    CONF_PATH.store(path as *mut c_char, Ordering::Release);
}

/// Reads a whole small file into `buf`; returns the bytes read.
fn read_file(path: *const c_char, buf: &mut [u8]) -> usize {
    // SAFETY: `path` is NUL-terminated.
    let fd = unsafe { crate::fs::open(path, sys::O_CLOEXEC, 0) };
    if fd < 0 {
        return 0;
    }
    let mut n = 0;
    while n < buf.len() {
        // SAFETY: the buffer is valid for the remaining length.
        match unsafe { sys::read(fd, buf[n..].as_mut_ptr(), buf.len() - n) } {
            Ok(0) => break,
            Ok(k) => n += k,
            Err(e) if e == Errno::EINTR => {}
            Err(_) => break,
        }
    }
    let _ = sys::close(fd);
    n
}

fn parse_u32(s: &[u8]) -> Option<u32> {
    if s.is_empty() || s.len() > 9 || !s.iter().all(u8::is_ascii_digit) {
        return None;
    }
    Some(s.iter().fold(0u32, |a, &d| a * 10 + (d - b'0') as u32))
}

fn load_config() -> Config {
    let mut cfg = Config {
        servers: [None; MAX_SERVERS],
        search: [([0; MAX_NAME + 1], 0); MAX_SEARCH],
        nsearch: 0,
        ndots: 1,
        timeout_ms: 5000,
        attempts: 2,
    };
    let mut buf = [0u8; 4096];
    let path = CONF_PATH.load(Ordering::Acquire);
    let path = if path.is_null() {
        c"/etc/resolv.conf".as_ptr()
    } else {
        path as *const c_char
    };
    let n = read_file(path, &mut buf);
    let mut nservers = 0;
    for line in buf[..n].split(|&b| b == b'\n') {
        let line = line
            .split(|&b| b == b'#' || b == b';')
            .next()
            .unwrap_or(b"");
        let mut words = line
            .split(|b| matches!(b, b' ' | b'\t' | b'\r'))
            .filter(|w| !w.is_empty());
        match words.next() {
            Some(b"nameserver") => {
                if let Some(w) = words.next()
                    && nservers < MAX_SERVERS
                    && let Some(server) = parse_server(w)
                {
                    cfg.servers[nservers] = Some(server);
                    nservers += 1;
                }
            }
            Some(b"search") | Some(b"domain") => {
                cfg.nsearch = 0;
                for w in words {
                    let w = w.strip_suffix(b".").unwrap_or(w);
                    if cfg.nsearch < MAX_SEARCH && !w.is_empty() && w.len() <= MAX_NAME {
                        cfg.search[cfg.nsearch].0[..w.len()].copy_from_slice(w);
                        cfg.search[cfg.nsearch].1 = w.len();
                        cfg.nsearch += 1;
                    }
                }
            }
            Some(b"options") => {
                for w in words {
                    if let Some(v) = w.strip_prefix(b"ndots:") {
                        cfg.ndots = parse_u32(v).unwrap_or(1).min(15);
                    } else if let Some(v) = w.strip_prefix(b"timeout:") {
                        cfg.timeout_ms = parse_u32(v).unwrap_or(5).clamp(1, 30) * 1000;
                    } else if let Some(v) = w.strip_prefix(b"attempts:") {
                        cfg.attempts = parse_u32(v).unwrap_or(2).clamp(1, 5);
                    }
                }
            }
            _ => {}
        }
    }
    if nservers == 0 {
        cfg.servers[0] = Some(Server {
            addr: Addr::V4([127, 0, 0, 1]),
            port: 53,
        });
    }
    cfg
}

/// Parses a `nameserver` value: an IPv4 or IPv6 address, optionally with
/// a port (`1.2.3.4:5353`, `[::1]:5353`).
fn parse_server(w: &[u8]) -> Option<Server> {
    let (host, port) = if let Some(rest) = w.strip_prefix(b"[") {
        let end = rest.iter().position(|&b| b == b']')?;
        let port = match &rest[end + 1..] {
            b"" => 53,
            p => u16::try_from(parse_u32(p.strip_prefix(b":")?)?).ok()?,
        };
        (&rest[..end], port)
    } else if w.iter().filter(|&&b| b == b':').count() == 1 {
        let i = w.iter().position(|&b| b == b':')?;
        (&w[..i], u16::try_from(parse_u32(&w[i + 1..])?).ok()?)
    } else {
        (w, 53)
    };
    // A zone index (`fe80::1%eth0`) is not supported; drop it.
    let host = host.split(|&b| b == b'%').next().unwrap_or(host);
    let addr = crate::socket::parse_ipv4(host)
        .map(Addr::V4)
        .or_else(|| crate::socket::parse_ipv6(host).map(Addr::V6))?;
    Some(Server { addr, port })
}

// ---------------------------------------------------------------------
// Messages.

/// Appends `name` in wire format to `out`. Returns the new length.
fn encode_name(name: &[u8], out: &mut [u8], mut pos: usize) -> Option<usize> {
    let name = name.strip_suffix(b".").unwrap_or(name);
    if name.is_empty() || name.len() > MAX_NAME {
        return None;
    }
    for label in name.split(|&b| b == b'.') {
        if label.is_empty()
            || label.len() > 63
            || !label
                .iter()
                .all(|&b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
        {
            return None;
        }
        if pos + 1 + label.len() > out.len() {
            return None;
        }
        out[pos] = label.len() as u8;
        out[pos + 1..pos + 1 + label.len()].copy_from_slice(label);
        pos += 1 + label.len();
    }
    if pos >= out.len() {
        return None;
    }
    out[pos] = 0;
    Some(pos + 1)
}

/// Builds a query for `name`/`qtype` with a random ID. Returns its length.
fn build_query(name: &[u8], qtype: u16, out: &mut [u8; UDP_MAX]) -> Option<usize> {
    let mut id = [0u8; 2];
    sys::getrandom_exact(&mut id).ok()?;
    out[..12].copy_from_slice(&[id[0], id[1], 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0]);
    let mut pos = encode_name(name, out, 12)?;
    if pos + 4 > out.len() {
        return None;
    }
    out[pos..pos + 2].copy_from_slice(&qtype.to_be_bytes());
    out[pos + 2..pos + 4].copy_from_slice(&CLASS_IN.to_be_bytes());
    pos += 4;
    Some(pos)
}

/// Reads a possibly compressed name at `pos`, writing it as dotted
/// lowercase text (no trailing dot) into `out`. Returns the text length
/// and the position just after the name's first (uncompressed) part.
fn read_name(msg: &[u8], mut pos: usize, out: &mut [u8; 256]) -> Option<(usize, usize)> {
    let mut len = 0;
    let mut after = None;
    // Every pointer must go backwards, so this many hops is plenty.
    let mut hops = 0;
    loop {
        let &b = msg.get(pos)?;
        if b & 0xc0 == 0xc0 {
            let target = ((b as usize & 0x3f) << 8) | *msg.get(pos + 1)? as usize;
            if target >= pos || hops >= 64 {
                return None;
            }
            hops += 1;
            after.get_or_insert(pos + 2);
            pos = target;
            continue;
        }
        if b & 0xc0 != 0 {
            return None;
        }
        pos += 1;
        if b == 0 {
            break;
        }
        let label = msg.get(pos..pos + b as usize)?;
        if len + label.len() + 1 > out.len() - 1 {
            return None;
        }
        if len > 0 {
            out[len] = b'.';
            len += 1;
        }
        for &c in label {
            out[len] = c.to_ascii_lowercase();
            len += 1;
        }
        pos += label.len();
    }
    Some((len, after.unwrap_or(pos)))
}

fn u16_at(msg: &[u8], pos: usize) -> Option<u16> {
    Some(u16::from_be_bytes([*msg.get(pos)?, *msg.get(pos + 1)?]))
}

/// A parsed record of interest.
#[derive(Clone, Copy)]
pub enum Record {
    /// An address record.
    Addr(Addr),
    /// A PTR target.
    Ptr,
}

/// Validates that `reply` answers `query` (ID and question) and returns
/// its RCODE and whether it was truncated.
fn check_reply(query: &[u8], reply: &[u8]) -> Option<(u8, bool)> {
    if reply.len() < 12 || reply[..2] != query[..2] || reply[2] & 0x80 == 0 {
        return None;
    }
    if u16_at(reply, 4)? != 1 {
        return None;
    }
    // The question must match ours (names compared case-insensitively:
    // servers may change the case).
    let mut qn = [0u8; 256];
    let mut rn = [0u8; 256];
    let (ql, qend) = read_name(query, 12, &mut qn)?;
    let (rl, rend) = read_name(reply, 12, &mut rn)?;
    if qn[..ql] != rn[..rl] || query.get(qend..qend + 4)? != reply.get(rend..rend + 4)? {
        return None;
    }
    Some((reply[3] & 0x0f, reply[2] & 0x02 != 0))
}

/// Extracts the answers of `reply` for the queried name: address records
/// (of `qtype`) or the PTR target, following a CNAME chain from the
/// queried name. The final owner name is left in `canon`.
fn parse_answers(
    reply: &[u8],
    qtype: u16,
    out: &mut dyn FnMut(Record, &[u8]),
    canon: &mut [u8; 256],
) -> Option<usize> {
    let ancount = u16_at(reply, 6)? as usize;
    let mut scratch = [0u8; 256];
    let (clen, mut pos) = read_name(reply, 12, canon)?;
    let mut clen = clen;
    pos += 4;
    for _ in 0..ancount {
        let (olen, next) = read_name(reply, pos, &mut scratch)?;
        let rtype = u16_at(reply, next)?;
        let rclass = u16_at(reply, next + 2)?;
        let rdlen = u16_at(reply, next + 8)? as usize;
        let rdata = next + 10;
        let data = reply.get(rdata..rdata + rdlen)?;
        pos = rdata + rdlen;
        if rclass != CLASS_IN || scratch[..olen] != canon[..clen] {
            continue;
        }
        match rtype {
            TYPE_CNAME => {
                let mut target = [0u8; 256];
                let (tl, _) = read_name(reply, rdata, &mut target)?;
                canon[..tl].copy_from_slice(&target[..tl]);
                clen = tl;
            }
            TYPE_A if qtype == TYPE_A && rdlen == 4 => {
                out(
                    Record::Addr(Addr::V4([data[0], data[1], data[2], data[3]])),
                    b"",
                );
            }
            TYPE_AAAA if qtype == TYPE_AAAA && rdlen == 16 => {
                let mut a = [0u8; 16];
                a.copy_from_slice(data);
                out(Record::Addr(Addr::V6(a)), b"");
            }
            TYPE_PTR if qtype == TYPE_PTR => {
                let mut target = [0u8; 256];
                let (tl, _) = read_name(reply, rdata, &mut target)?;
                out(Record::Ptr, &target[..tl]);
            }
            _ => {}
        }
    }
    Some(clen)
}

// ---------------------------------------------------------------------
// Transport.

fn now_ms() -> u64 {
    let t = sys::clock_gettime(sys::CLOCK_MONOTONIC).unwrap_or_default();
    t.tv_sec as u64 * 1000 + t.tv_nsec as u64 / 1_000_000
}

/// A server's address as a sockaddr.
fn sockaddr(server: Server) -> ([u8; 28], usize) {
    let mut buf = [0u8; 28];
    let port = server.port.to_be();
    match server.addr {
        Addr::V4(a) => {
            let sa = SockaddrIn {
                sin_family: AF_INET as u16,
                sin_port: port,
                sin_addr: a,
                sin_zero: [0; 8],
            };
            // SAFETY: plain data of 16 bytes.
            buf[..16].copy_from_slice(unsafe { &*(&sa as *const SockaddrIn as *const [u8; 16]) });
            (buf, 16)
        }
        Addr::V6(a) => {
            let sa = SockaddrIn6 {
                sin6_family: AF_INET6 as u16,
                sin6_port: port,
                sin6_flowinfo: 0,
                sin6_addr: a,
                sin6_scope_id: 0,
            };
            // SAFETY: plain data of 28 bytes.
            buf.copy_from_slice(unsafe { &*(&sa as *const SockaddrIn6 as *const [u8; 28]) });
            (buf, 28)
        }
    }
}

/// The server a datagram came from, if it is one we asked.
fn sender(servers: &[Option<Server>], sa: &[u8; 28], len: usize) -> Option<Server> {
    let family = u16::from_le_bytes([sa[0], sa[1]]) as c_int;
    let addr = match family {
        AF_INET if len >= 16 => Addr::V4([sa[4], sa[5], sa[6], sa[7]]),
        AF_INET6 if len >= 28 => {
            let mut a = [0u8; 16];
            a.copy_from_slice(&sa[8..24]);
            Addr::V6(a)
        }
        _ => return None,
    };
    let port = u16::from_be_bytes([sa[2], sa[3]]);
    servers
        .iter()
        .flatten()
        .copied()
        .find(|s| s.addr == addr && s.port == port)
}

/// One outstanding query.
struct Pending {
    query: [u8; UDP_MAX],
    qlen: usize,
    reply: [u8; UDP_MAX],
    rlen: usize,
    /// RCODE of the accepted reply, or `None` while waiting.
    rcode: Option<u8>,
    /// A truncated UDP reply: ask this server over TCP.
    need_tcp: Option<Server>,
}

/// Sends the queries to every server and collects replies.
fn exchange(cfg: &Config, pending: &mut [Pending]) -> Result<(), Error> {
    let want4 = cfg
        .servers
        .iter()
        .flatten()
        .any(|s| matches!(s.addr, Addr::V4(_)));
    let want6 = cfg
        .servers
        .iter()
        .flatten()
        .any(|s| matches!(s.addr, Addr::V6(_)));
    let open = |family: c_int| -> Option<c_int> {
        // SAFETY: no memory is involved.
        let fd =
            unsafe { crate::socket::socket(family, SOCK_DGRAM | SOCK_CLOEXEC | SOCK_NONBLOCK, 0) };
        if fd < 0 { None } else { Some(fd) }
    };
    let fd4 = if want4 { open(AF_INET) } else { None };
    let fd6 = if want6 { open(AF_INET6) } else { None };
    if fd4.is_none() && fd6.is_none() {
        return Err(Error::Again);
    }
    let mut fds = [PollFd {
        fd: -1,
        events: POLLIN,
        revents: 0,
    }; 2];
    let mut nfds = 0;
    for fd in [fd4, fd6].into_iter().flatten() {
        fds[nfds].fd = fd;
        nfds += 1;
    }
    let result = exchange_on(cfg, pending, &mut fds[..nfds], fd4, fd6);
    for fd in [fd4, fd6].into_iter().flatten() {
        let _ = sys::close(fd);
    }
    result
}

fn exchange_on(
    cfg: &Config,
    pending: &mut [Pending],
    fds: &mut [PollFd],
    fd4: Option<c_int>,
    fd6: Option<c_int>,
) -> Result<(), Error> {
    for _attempt in 0..cfg.attempts {
        // (Re)send everything still unanswered to every server.
        for p in pending.iter_mut().filter(|p| p.rcode.is_none()) {
            for s in cfg.servers.iter().flatten() {
                let fd = match s.addr {
                    Addr::V4(_) => fd4,
                    Addr::V6(_) => fd6,
                };
                let Some(fd) = fd else { continue };
                let (sa, salen) = sockaddr(*s);
                // SAFETY: valid buffers.
                let _ = unsafe {
                    crate::socket::sendto(
                        fd,
                        p.query.as_ptr() as *const c_void,
                        p.qlen,
                        0,
                        sa.as_ptr() as *const c_void,
                        salen as u32,
                    )
                };
            }
        }
        let deadline = now_ms() + cfg.timeout_ms as u64;
        loop {
            if pending.iter().all(|p| p.rcode.is_some()) {
                return Ok(());
            }
            let now = now_ms();
            if now >= deadline {
                break;
            }
            // SAFETY: valid pollfd array.
            let r = unsafe {
                crate::poll::poll(
                    fds.as_mut_ptr(),
                    fds.len() as u32,
                    (deadline - now) as c_int,
                )
            };
            if r < 0 {
                if Errno::get() == Errno::EINTR {
                    continue;
                }
                return Err(Error::Again);
            }
            if r == 0 {
                break;
            }
            for fd in fds.iter().filter(|f| f.revents != 0).map(|f| f.fd) {
                loop {
                    let mut buf = [0u8; UDP_MAX];
                    let mut sa = [0u8; 28];
                    let mut salen: u32 = 28;
                    // SAFETY: valid buffers.
                    let n = unsafe {
                        crate::socket::recvfrom(
                            fd,
                            buf.as_mut_ptr() as *mut c_void,
                            buf.len(),
                            0,
                            sa.as_mut_ptr() as *mut c_void,
                            &mut salen,
                        )
                    };
                    if n < 0 {
                        break;
                    }
                    let n = n as usize;
                    let Some(from) = sender(&cfg.servers, &sa, salen as usize) else {
                        continue;
                    };
                    let reply = &buf[..n];
                    for p in pending.iter_mut().filter(|p| p.rcode.is_none()) {
                        let Some((rcode, truncated)) = check_reply(&p.query[..p.qlen], reply)
                        else {
                            continue;
                        };
                        match rcode {
                            0 | 3 => {
                                if truncated {
                                    p.need_tcp = Some(from);
                                    p.rcode = Some(rcode);
                                } else {
                                    p.reply[..n].copy_from_slice(reply);
                                    p.rlen = n;
                                    p.rcode = Some(rcode);
                                }
                            }
                            // SERVFAIL and the like: wait for another server.
                            _ => {}
                        }
                        break;
                    }
                }
            }
        }
    }
    if pending.iter().any(|p| p.rcode.is_some()) {
        Ok(())
    } else {
        Err(Error::Again)
    }
}

/// Asks `server` over TCP; the reply (without the length prefix) is
/// written to a `malloc`ed buffer returned with its length.
fn tcp_query(server: Server, query: &[u8], timeout_ms: u32) -> Option<(*mut u8, usize)> {
    let family = match server.addr {
        Addr::V4(_) => AF_INET,
        Addr::V6(_) => AF_INET6,
    };
    // SAFETY: no memory is involved.
    let fd =
        unsafe { crate::socket::socket(family, SOCK_STREAM | SOCK_CLOEXEC | SOCK_NONBLOCK, 0) };
    if fd < 0 {
        return None;
    }
    let result = tcp_query_on(fd, server, query, timeout_ms);
    let _ = sys::close(fd);
    result
}

fn wait_fd(fd: c_int, events: i16, deadline: u64) -> bool {
    loop {
        let now = now_ms();
        if now >= deadline {
            return false;
        }
        let mut p = [PollFd {
            fd,
            events,
            revents: 0,
        }];
        // SAFETY: valid pollfd.
        let r = unsafe { crate::poll::poll(p.as_mut_ptr(), 1, (deadline - now) as c_int) };
        if r > 0 {
            return true;
        }
        if r < 0 && Errno::get() != Errno::EINTR {
            return false;
        }
        if r == 0 {
            return false;
        }
    }
}

fn tcp_query_on(
    fd: c_int,
    server: Server,
    query: &[u8],
    timeout_ms: u32,
) -> Option<(*mut u8, usize)> {
    let deadline = now_ms() + timeout_ms as u64;
    let (sa, salen) = sockaddr(server);
    // SAFETY: valid sockaddr.
    if unsafe { crate::socket::connect(fd, sa.as_ptr() as *const c_void, salen as u32) } < 0
        && (Errno::get() != Errno::EINPROGRESS || !wait_fd(fd, POLLOUT, deadline))
    {
        return None;
    }
    // Length prefix and query in one write (they always fit a segment).
    let mut msg = [0u8; UDP_MAX + 2];
    msg[..2].copy_from_slice(&(query.len() as u16).to_be_bytes());
    msg[2..2 + query.len()].copy_from_slice(query);
    let mut sent = 0;
    while sent < 2 + query.len() {
        if !wait_fd(fd, POLLOUT, deadline) {
            return None;
        }
        // SAFETY: valid buffer.
        match unsafe { sys::write(fd, msg[sent..].as_ptr(), 2 + query.len() - sent) } {
            Ok(n) => sent += n,
            Err(e) if e == Errno::EINTR || e == Errno::EAGAIN => {}
            Err(_) => return None,
        }
    }
    let mut lenbuf = [0u8; 2];
    read_exact(fd, &mut lenbuf, deadline)?;
    let len = u16::from_be_bytes(lenbuf) as usize;
    if len < 12 {
        return None;
    }
    let buf = crate::malloc::alloc(len);
    if buf.is_null() {
        return None;
    }
    // SAFETY: `len` bytes were allocated.
    let slice = unsafe { core::slice::from_raw_parts_mut(buf, len) };
    if read_exact(fd, slice, deadline).is_none() {
        // SAFETY: our block.
        unsafe { crate::malloc::dealloc(buf) };
        return None;
    }
    Some((buf, len))
}

fn read_exact(fd: c_int, buf: &mut [u8], deadline: u64) -> Option<()> {
    let mut got = 0;
    while got < buf.len() {
        if !wait_fd(fd, POLLIN, deadline) {
            return None;
        }
        // SAFETY: valid buffer.
        match unsafe { sys::read(fd, buf[got..].as_mut_ptr(), buf.len() - got) } {
            Ok(0) => return None,
            Ok(n) => got += n,
            Err(e) if e == Errno::EINTR || e == Errno::EAGAIN => {}
            Err(_) => return None,
        }
    }
    Some(())
}

// ---------------------------------------------------------------------
// Lookups.

/// Runs one set of queries (`qtypes`) for `name` and feeds the records
/// to `out`. `canon` receives the canonical name.
fn query(
    cfg: &Config,
    name: &[u8],
    qtypes: &[u16],
    out: &mut dyn FnMut(Record, &[u8]),
    canon: &mut [u8; 256],
) -> Result<usize, Error> {
    let mut pending: [Pending; 2] = core::array::from_fn(|_| Pending {
        query: [0; UDP_MAX],
        qlen: 0,
        reply: [0; UDP_MAX],
        rlen: 0,
        rcode: None,
        need_tcp: None,
    });
    let n = qtypes.len().min(2);
    for (p, &t) in pending.iter_mut().zip(qtypes) {
        // A name that cannot be encoded does not exist.
        p.qlen = build_query(name, t, &mut p.query).ok_or(Error::NoName)?;
    }
    exchange(cfg, &mut pending[..n])?;
    let mut clen = 0;
    let mut found_records = false;
    let mut nxdomain = 0;
    let mut answered = 0;
    for (p, &t) in pending[..n].iter().zip(qtypes) {
        let Some(rcode) = p.rcode else { continue };
        answered += 1;
        if rcode == 3 {
            nxdomain += 1;
            continue;
        }
        let mut count = 0;
        let mut sink = |r: Record, s: &[u8]| {
            count += 1;
            out(r, s);
        };
        let parsed = if let Some(server) = p.need_tcp {
            match tcp_query(server, &p.query[..p.qlen], cfg.timeout_ms) {
                Some((buf, len)) => {
                    // SAFETY: the block holds `len` bytes.
                    let reply = unsafe { core::slice::from_raw_parts(buf, len) };
                    let r = match check_reply(&p.query[..p.qlen], reply) {
                        Some((0, _)) => parse_answers(reply, t, &mut sink, canon),
                        _ => None,
                    };
                    // SAFETY: our block.
                    unsafe { crate::malloc::dealloc(buf) };
                    r
                }
                None => None,
            }
        } else {
            parse_answers(&p.reply[..p.rlen], t, &mut sink, canon)
        };
        match parsed {
            Some(l) => clen = l,
            None => return Err(Error::Fail),
        }
        if count > 0 {
            found_records = true;
        }
    }
    if found_records {
        return Ok(clen);
    }
    if answered == 0 {
        Err(Error::Again)
    } else if nxdomain == answered {
        Err(Error::NoName)
    } else {
        // Answered without records: no data of these types.
        Err(Error::NoName)
    }
}

/// Resolves `name` to addresses, applying the search list. Returns the
/// number of addresses stored in `out` and leaves the canonical name in
/// `canon` (its length is returned alongside).
pub fn lookup(
    name: &[u8],
    want4: bool,
    want6: bool,
    out: &mut [Option<Addr>],
    canon: &mut [u8; 256],
) -> Result<(usize, usize), Error> {
    if name.is_empty() || name.len() > MAX_NAME + 1 {
        return Err(Error::NoName);
    }
    let cfg = load_config();
    let mut qtypes = [0u16; 2];
    let mut nq = 0;
    if want4 {
        qtypes[nq] = TYPE_A;
        nq += 1;
    }
    if want6 {
        qtypes[nq] = TYPE_AAAA;
        nq += 1;
    }
    let absolute = name.ends_with(b".");
    let dots = name.iter().filter(|&&b| b == b'.').count() as u32;
    let try_name = |candidate: &[u8],
                    out: &mut [Option<Addr>],
                    canon: &mut [u8; 256]|
     -> Result<(usize, usize), Error> {
        let mut count = 0;
        let mut sink = |r: Record, _: &[u8]| {
            if let Record::Addr(a) = r
                && count < out.len()
            {
                out[count] = Some(a);
                count += 1;
            }
        };
        let clen = query(&cfg, candidate, &qtypes[..nq], &mut sink, canon)?;
        Ok((count, clen))
    };
    if absolute || cfg.nsearch == 0 {
        return try_name(name, out, canon);
    }
    let mut buf = [0u8; 2 * MAX_NAME + 2];
    let mut last = Err(Error::NoName);
    let search_first = dots < cfg.ndots;
    for round in 0..2 {
        if (round == 0) == search_first {
            for (dom, dl) in &cfg.search[..cfg.nsearch] {
                if name.len() + 1 + dl > MAX_NAME {
                    continue;
                }
                buf[..name.len()].copy_from_slice(name);
                buf[name.len()] = b'.';
                buf[name.len() + 1..name.len() + 1 + dl].copy_from_slice(&dom[..*dl]);
                match try_name(&buf[..name.len() + 1 + dl], out, canon) {
                    Err(Error::NoName) => last = Err(Error::NoName),
                    r => return r,
                }
            }
        } else {
            match try_name(name, out, canon) {
                Err(Error::NoName) => last = Err(Error::NoName),
                r => return r,
            }
        }
    }
    last
}

/// Reverse lookup: the PTR name for `addr`, written to `out`.
pub fn reverse(addr: Addr, out: &mut [u8; 256]) -> Result<usize, Error> {
    let mut qname = [0u8; 80];
    let mut n = 0;
    let mut push = |s: &[u8]| {
        qname[n..n + s.len()].copy_from_slice(s);
        n += s.len();
    };
    match addr {
        Addr::V4(a) => {
            for (i, b) in a.iter().rev().enumerate() {
                let mut d = [0u8; 3];
                let mut k = 0;
                let mut v = *b;
                loop {
                    d[k] = b'0' + v % 10;
                    k += 1;
                    v /= 10;
                    if v == 0 {
                        break;
                    }
                }
                d[..k].reverse();
                push(&d[..k]);
                if i < 3 {
                    push(b".");
                }
            }
            push(b".in-addr.arpa");
        }
        Addr::V6(a) => {
            const HEX: &[u8; 16] = b"0123456789abcdef";
            for b in a.iter().rev() {
                push(&[HEX[(b & 0xf) as usize], b'.', HEX[(b >> 4) as usize], b'.']);
            }
            push(b"ip6.arpa");
        }
    }
    let cfg = load_config();
    let mut found = 0;
    let mut sink = |r: Record, s: &[u8]| {
        if let Record::Ptr = r
            && found == 0
        {
            out[..s.len()].copy_from_slice(s);
            found = s.len();
        }
    };
    let mut canon = [0u8; 256];
    query(&cfg, &qname[..n], &[TYPE_PTR], &mut sink, &mut canon)?;
    if found == 0 {
        Err(Error::NoName)
    } else {
        Ok(found)
    }
}

/// `res_init(3)`: configuration is re-read on every lookup, so there is
/// nothing to do.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn res_init() -> c_int {
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_round_trip_and_reject_garbage() {
        let mut buf = [0u8; 512];
        let n = encode_name(b"www.Example.com.", &mut buf, 0).unwrap();
        assert_eq!(&buf[..n], b"\x03www\x07Example\x03com\x00");
        let mut out = [0u8; 256];
        let (len, after) = read_name(&buf, 0, &mut out).unwrap();
        assert_eq!(&out[..len], b"www.example.com");
        assert_eq!(after, n);
        assert!(encode_name(b"", &mut buf, 0).is_none());
        assert!(encode_name(b"a..b", &mut buf, 0).is_none());
        assert!(encode_name(b"bad name", &mut buf, 0).is_none());
        assert!(encode_name(&[b'a'; 64], &mut buf, 0).is_none());
        // Compression pointer loops and forward pointers are rejected.
        assert!(read_name(b"\xc0\x00", 0, &mut out).is_none());
        assert!(read_name(b"\x01a\xc0\x05", 0, &mut out).is_none());
        // A valid pointer to an earlier name.
        let msg = b"\x03foo\x00\x03bar\xc0\x00";
        let (len, after) = read_name(msg, 5, &mut out).unwrap();
        assert_eq!(&out[..len], b"bar.foo");
        assert_eq!(after, 11);
    }

    #[test]
    fn replies_are_checked_and_parsed() {
        let mut q = [0u8; UDP_MAX];
        let qlen = build_query(b"a.example", TYPE_A, &mut q).unwrap();
        // Reply: same id, QR, RD/RA, 1 question, 3 answers: CNAME chain then A.
        let mut r = Vec::new();
        r.extend_from_slice(&q[..2]);
        r.extend_from_slice(&[0x81, 0x80, 0, 1, 0, 3, 0, 0, 0, 0]);
        r.extend_from_slice(&q[12..qlen]);
        let rr = |r: &mut Vec<u8>, owner: &[u8], t: u16, data: &[u8]| {
            r.extend_from_slice(owner);
            r.extend_from_slice(&t.to_be_bytes());
            r.extend_from_slice(&1u16.to_be_bytes());
            r.extend_from_slice(&300u32.to_be_bytes());
            r.extend_from_slice(&(data.len() as u16).to_be_bytes());
            r.extend_from_slice(data);
        };
        rr(&mut r, b"\xc0\x0c", TYPE_CNAME, b"\x01b\x07example\x00");
        // An unrelated record must be ignored.
        rr(&mut r, b"\x05other\x07example\x00", TYPE_A, &[9, 9, 9, 9]);
        rr(&mut r, b"\x01b\x07example\x00", TYPE_A, &[10, 1, 2, 3]);
        assert_eq!(check_reply(&q[..qlen], &r), Some((0, false)));
        let mut got = Vec::new();
        let mut canon = [0u8; 256];
        let clen = parse_answers(&r, TYPE_A, &mut |rec, _| got.push(rec), &mut canon).unwrap();
        assert_eq!(&canon[..clen], b"b.example");
        assert_eq!(got.len(), 1);
        assert!(matches!(got[0], Record::Addr(Addr::V4([10, 1, 2, 3]))));
        // Wrong id, wrong question, or a query (not a response) are rejected.
        let mut bad = r.clone();
        bad[0] ^= 1;
        assert!(check_reply(&q[..qlen], &bad).is_none());
        let mut bad = r.clone();
        bad[2] = 0x01;
        assert!(check_reply(&q[..qlen], &bad).is_none());
        let mut bad = r.clone();
        bad[14] = b'x';
        assert!(check_reply(&q[..qlen], &bad).is_none());
        // Truncated records fail cleanly.
        assert!(parse_answers(&r[..r.len() - 2], TYPE_A, &mut |_, _| {}, &mut canon).is_none());
    }

    #[test]
    fn config_parsing() {
        let dir = std::env::temp_dir().join(format!("rustlibc-resolv-{}", std::process::id()));
        std::fs::write(
            &dir,
            "# comment\nnameserver 10.0.0.1\nnameserver [::1]:5353 ; trailing\nsearch example.com corp.\noptions ndots:2 timeout:3 attempts:4\nnameserver 10.0.0.2\nnameserver 10.0.0.3\n",
        )
        .unwrap();
        let path = std::ffi::CString::new(dir.to_str().unwrap()).unwrap();
        // SAFETY: the path outlives the test.
        unsafe { __rustlibc_set_resolv_conf(path.as_ptr()) };
        let cfg = load_config();
        // SAFETY: restore the default.
        unsafe { __rustlibc_set_resolv_conf(ptr::null()) };
        std::fs::remove_file(&dir).unwrap();
        assert!(matches!(
            cfg.servers[0],
            Some(Server {
                addr: Addr::V4([10, 0, 0, 1]),
                port: 53
            })
        ));
        assert!(matches!(
            cfg.servers[1],
            Some(Server {
                addr: Addr::V6(_),
                port: 5353
            })
        ));
        assert!(matches!(
            cfg.servers[2],
            Some(Server {
                addr: Addr::V4([10, 0, 0, 2]),
                port: 53
            })
        ));
        assert_eq!(cfg.nsearch, 2);
        assert_eq!(&cfg.search[0].0[..cfg.search[0].1], b"example.com");
        assert_eq!(&cfg.search[1].0[..cfg.search[1].1], b"corp");
        assert_eq!((cfg.ndots, cfg.timeout_ms, cfg.attempts), (2, 3000, 4));
    }
}
