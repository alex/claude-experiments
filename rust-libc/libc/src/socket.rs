//! `<sys/socket.h>`, `<arpa/inet.h>` and `<netdb.h>`.
//!
//! The socket calls are thin syscall wrappers. Address conversion
//! (`inet_pton`/`inet_ntop`) is implemented here. Name resolution is
//! deliberately minimal: `getaddrinfo` handles numeric addresses,
//! `localhost`, `/etc/hosts` and then DNS (see `resolv.rs`).

use crate::c_char;
use crate::errno::{CReturnOr, Errno};
use crate::malloc;
use crate::sys::{self, Timespec};
use core::ffi::{c_int, c_void};
use core::ptr;

use crate::arch::nr;

/// `socklen_t`.
pub type Socklen = u32;

#[allow(missing_docs)]
pub const AF_UNSPEC: c_int = 0;
#[allow(missing_docs)]
pub const AF_UNIX: c_int = 1;
#[allow(missing_docs)]
pub const AF_INET: c_int = 2;
#[allow(missing_docs)]
pub const AF_INET6: c_int = 10;
#[allow(missing_docs)]
pub const SOCK_STREAM: c_int = 1;
#[allow(missing_docs)]
pub const SOCK_DGRAM: c_int = 2;
#[allow(missing_docs)]
pub const SOCK_RAW: c_int = 3;
#[allow(missing_docs)]
pub const IPPROTO_TCP: c_int = 6;
#[allow(missing_docs)]
pub const IPPROTO_UDP: c_int = 17;

macro_rules! syscalls {
    ($($(#[$doc:meta])* pub unsafe fn $name:ident($($arg:ident: $ty:ty),*) = $nr:expr => $ret:ty;)*) => {
        $(
            $(#[$doc])*
            ///
            /// # Safety
            /// Pointer arguments must be valid for what the kernel does with them.
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub unsafe extern "C" fn $name($($arg: $ty),*) -> $ret {
                // SAFETY: caller contract.
                let r = unsafe { crate::arch::syscall_n($nr, &[$($arg as usize),*]) };
                sys::check(r).map(|v| v as $ret).c_ret_or(-1)
            }
        )*
    };
}

syscalls! {
    /// `socket(2)`.
    pub unsafe fn socket(domain: c_int, kind: c_int, protocol: c_int) = nr::SOCKET => c_int;
    /// `socketpair(2)`.
    pub unsafe fn socketpair(domain: c_int, kind: c_int, protocol: c_int, fds: *mut c_int) = nr::SOCKETPAIR => c_int;
    /// `bind(2)`.
    pub unsafe fn bind(fd: c_int, addr: *const c_void, len: Socklen) = nr::BIND => c_int;
    /// `listen(2)`.
    pub unsafe fn listen(fd: c_int, backlog: c_int) = nr::LISTEN => c_int;
    /// `accept4(2)`.
    pub unsafe fn accept4(fd: c_int, addr: *mut c_void, len: *mut Socklen, flags: c_int) = nr::ACCEPT4 => c_int;
    /// `connect(2)`.
    pub unsafe fn connect(fd: c_int, addr: *const c_void, len: Socklen) = nr::CONNECT => c_int;
    /// `sendto(2)`.
    pub unsafe fn sendto(fd: c_int, buf: *const c_void, len: usize, flags: c_int, addr: *const c_void, addrlen: Socklen) = nr::SENDTO => isize;
    /// `recvfrom(2)`.
    pub unsafe fn recvfrom(fd: c_int, buf: *mut c_void, len: usize, flags: c_int, addr: *mut c_void, addrlen: *mut Socklen) = nr::RECVFROM => isize;
    /// `sendmsg(2)`.
    pub unsafe fn sendmsg(fd: c_int, msg: *const c_void, flags: c_int) = nr::SENDMSG => isize;
    /// `recvmsg(2)`.
    pub unsafe fn recvmsg(fd: c_int, msg: *mut c_void, flags: c_int) = nr::RECVMSG => isize;
    /// `shutdown(2)`.
    pub unsafe fn shutdown(fd: c_int, how: c_int) = nr::SHUTDOWN => c_int;
    /// `getsockname(2)`.
    pub unsafe fn getsockname(fd: c_int, addr: *mut c_void, len: *mut Socklen) = nr::GETSOCKNAME => c_int;
    /// `getpeername(2)`.
    pub unsafe fn getpeername(fd: c_int, addr: *mut c_void, len: *mut Socklen) = nr::GETPEERNAME => c_int;
    /// `setsockopt(2)`.
    pub unsafe fn setsockopt(fd: c_int, level: c_int, name: c_int, value: *const c_void, len: Socklen) = nr::SETSOCKOPT => c_int;
    /// `getsockopt(2)`.
    pub unsafe fn getsockopt(fd: c_int, level: c_int, name: c_int, value: *mut c_void, len: *mut Socklen) = nr::GETSOCKOPT => c_int;
}

/// `accept(2)`.
///
/// # Safety
/// `addr` and `len` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn accept(fd: c_int, addr: *mut c_void, len: *mut Socklen) -> c_int {
    // SAFETY: forwarded.
    unsafe { accept4(fd, addr, len, 0) }
}

/// `send(2)`.
///
/// # Safety
/// `buf` must be valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn send(fd: c_int, buf: *const c_void, len: usize, flags: c_int) -> isize {
    // SAFETY: forwarded.
    unsafe { sendto(fd, buf, len, flags, ptr::null(), 0) }
}

/// `recv(2)`.
///
/// # Safety
/// `buf` must be valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn recv(fd: c_int, buf: *mut c_void, len: usize, flags: c_int) -> isize {
    // SAFETY: forwarded.
    unsafe { recvfrom(fd, buf, len, flags, ptr::null_mut(), ptr::null_mut()) }
}

/// `htons(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn htons(v: u16) -> u16 {
    v.to_be()
}
/// `ntohs(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ntohs(v: u16) -> u16 {
    u16::from_be(v)
}
/// `htonl(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn htonl(v: u32) -> u32 {
    v.to_be()
}
/// `ntohl(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ntohl(v: u32) -> u32 {
    u32::from_be(v)
}

/// `in6addr_any`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static in6addr_any: [u8; 16] = [0; 16];
/// `in6addr_loopback`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static in6addr_loopback: [u8; 16] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];

// ---------------------------------------------------------------------
// Address text conversion.

/// Parses a dotted-quad IPv4 address strictly (four decimal parts of at
/// most three digits, no leading zeros, each at most 255).
pub fn parse_ipv4(s: &[u8]) -> Option<[u8; 4]> {
    let mut out = [0u8; 4];
    let mut parts = s.split(|&b| b == b'.');
    for slot in &mut out {
        let p = parts.next()?;
        if p.is_empty()
            || p.len() > 3
            || !p.iter().all(u8::is_ascii_digit)
            || (p.len() > 1 && p[0] == b'0')
        {
            return None;
        }
        let v: u32 = p.iter().fold(0, |a, &d| a * 10 + (d - b'0') as u32);
        *slot = u8::try_from(v).ok()?;
    }
    if parts.next().is_some() {
        return None;
    }
    Some(out)
}

/// Parses an IPv6 address in RFC 4291 text form (with `::` compression
/// and an optional embedded dotted-quad).
pub fn parse_ipv6(s: &[u8]) -> Option<[u8; 16]> {
    let mut groups = [0u16; 8];
    let mut n = 0usize; // groups filled before "::"
    let mut tail = [0u16; 8];
    let mut ntail = 0usize;
    let mut seen_gap = false;
    let mut i = 0;
    if s.starts_with(b"::") {
        seen_gap = true;
        i = 2;
    } else if s.starts_with(b":") {
        return None;
    }
    while i < s.len() {
        // A group is up to 4 hex digits, or a dotted quad in last position.
        let start = i;
        while i < s.len() && s[i] != b':' {
            i += 1;
        }
        let g = &s[start..i];
        if g.is_empty() {
            return None;
        }
        let value = if g.contains(&b'.') {
            let v4 = parse_ipv4(g)?;
            if i != s.len() {
                return None;
            }
            let (hi, lo) = (
                u16::from_be_bytes([v4[0], v4[1]]),
                u16::from_be_bytes([v4[2], v4[3]]),
            );
            push(&mut groups, &mut n, &mut tail, &mut ntail, seen_gap, hi)?;
            lo
        } else {
            if g.len() > 4 || !g.iter().all(u8::is_ascii_hexdigit) {
                return None;
            }
            g.iter().fold(0u16, |a, &d| {
                a * 16 + (d as char).to_digit(16).unwrap() as u16
            })
        };
        push(&mut groups, &mut n, &mut tail, &mut ntail, seen_gap, value)?;
        if i < s.len() {
            i += 1; // ':'
            if i < s.len() && s[i] == b':' {
                if seen_gap {
                    return None;
                }
                seen_gap = true;
                i += 1;
            } else if i == s.len() {
                return None; // trailing single ':'
            }
        }
    }
    if !seen_gap && n != 8 {
        return None;
    }
    if seen_gap && n + ntail >= 8 {
        return None;
    }
    let mut out = [0u8; 16];
    for (k, g) in groups[..n].iter().enumerate() {
        out[2 * k..2 * k + 2].copy_from_slice(&g.to_be_bytes());
    }
    for (k, g) in tail[..ntail].iter().enumerate() {
        let pos = 8 - ntail + k;
        out[2 * pos..2 * pos + 2].copy_from_slice(&g.to_be_bytes());
    }
    Some(out)
}

fn push(
    groups: &mut [u16; 8],
    n: &mut usize,
    tail: &mut [u16; 8],
    ntail: &mut usize,
    gap: bool,
    v: u16,
) -> Option<()> {
    if gap {
        if *n + *ntail >= 7 {
            return None;
        }
        tail[*ntail] = v;
        *ntail += 1;
    } else {
        if *n >= 8 {
            return None;
        }
        groups[*n] = v;
        *n += 1;
    }
    Some(())
}

/// Formats an IPv4 address.
pub fn format_ipv4(a: [u8; 4], out: &mut [u8]) -> Option<usize> {
    let mut buf = [0u8; 20];
    let mut w = crate::fmt::SliceWriter::new(&mut buf);
    core::fmt::write(&mut w, format_args!("{}.{}.{}.{}", a[0], a[1], a[2], a[3])).ok()?;
    let n = w.len();
    if n + 1 > out.len() {
        return None;
    }
    out[..n].copy_from_slice(&buf[..n]);
    Some(n)
}

/// Formats an IPv6 address per RFC 5952 (lowercase, longest zero run
/// compressed, IPv4-mapped addresses in dotted form).
pub fn format_ipv6(a: [u8; 16], out: &mut [u8]) -> Option<usize> {
    let groups: [u16; 8] = core::array::from_fn(|i| u16::from_be_bytes([a[2 * i], a[2 * i + 1]]));
    let mut buf = [0u8; 48];
    let mut w = crate::fmt::SliceWriter::new(&mut buf);
    let mapped = groups[..5] == [0; 5] && groups[5] == 0xffff;
    // Longest run of zero groups (length >= 2).
    let (mut best_start, mut best_len) = (usize::MAX, 0);
    let mut i = 0;
    let limit = if mapped { 6 } else { 8 };
    while i < limit {
        if groups[i] == 0 {
            let start = i;
            while i < limit && groups[i] == 0 {
                i += 1;
            }
            if i - start > best_len && i - start >= 2 {
                best_start = start;
                best_len = i - start;
            }
        } else {
            i += 1;
        }
    }
    let mut k = 0;
    while k < limit {
        if k == best_start {
            // The run is written as "::"; neighbours add no separator.
            let _ = w.write_str("::");
            k += best_len;
            continue;
        }
        let _ = core::fmt::write(&mut w, format_args!("{:x}", groups[k]));
        if k + 1 < limit && k + 1 != best_start {
            let _ = w.write_str(":");
        }
        k += 1;
    }
    if mapped {
        let _ = w.write_str(":");
        let _ = core::fmt::write(
            &mut w,
            format_args!("{}.{}.{}.{}", a[12], a[13], a[14], a[15]),
        );
    }
    let n = w.len();
    if n + 1 > out.len() {
        return None;
    }
    out[..n].copy_from_slice(&buf[..n]);
    Some(n)
}

use core::fmt::Write as _;

/// `inet_pton(3)`.
///
/// # Safety
/// `src` must be NUL-terminated; `dst` valid for 4 or 16 bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn inet_pton(af: c_int, src: *const c_char, dst: *mut c_void) -> c_int {
    // SAFETY: caller contract.
    let s = unsafe {
        core::slice::from_raw_parts(
            src as *const u8,
            crate::string::search::strlen(src as *const u8),
        )
    };
    match af {
        AF_INET => match parse_ipv4(s) {
            Some(a) => {
                // SAFETY: caller contract.
                unsafe { ptr::copy_nonoverlapping(a.as_ptr(), dst as *mut u8, 4) };
                1
            }
            None => 0,
        },
        AF_INET6 => match parse_ipv6(s) {
            Some(a) => {
                // SAFETY: caller contract.
                unsafe { ptr::copy_nonoverlapping(a.as_ptr(), dst as *mut u8, 16) };
                1
            }
            None => 0,
        },
        _ => {
            Errno::EAFNOSUPPORT.set();
            -1
        }
    }
}

/// `inet_ntop(3)`.
///
/// # Safety
/// `src` must point to 4 or 16 bytes; `dst` valid for `size` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn inet_ntop(
    af: c_int,
    src: *const c_void,
    dst: *mut c_char,
    size: Socklen,
) -> *const c_char {
    // SAFETY: caller contract.
    let out = unsafe { core::slice::from_raw_parts_mut(dst as *mut u8, size as usize) };
    let n = match af {
        // SAFETY: caller contract.
        AF_INET => format_ipv4(unsafe { *(src as *const [u8; 4]) }, out),
        // SAFETY: caller contract.
        AF_INET6 => format_ipv6(unsafe { *(src as *const [u8; 16]) }, out),
        _ => {
            Errno::EAFNOSUPPORT.set();
            return ptr::null();
        }
    };
    match n {
        Some(n) => {
            out[n] = 0;
            dst
        }
        None => {
            Errno::ENOSPC.set();
            ptr::null()
        }
    }
}

/// `inet_aton(3)`: accepts the classic `a`, `a.b`, `a.b.c` and
/// `a.b.c.d` forms with octal and hex parts.
///
/// # Safety
/// `s` must be NUL-terminated; `out` valid for 4 bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn inet_aton(s: *const c_char, out: *mut u32) -> c_int {
    let mut parts = [0u64; 4];
    let mut n = 0;
    let mut p = s;
    loop {
        let mut end: *mut c_char = ptr::null_mut();
        // SAFETY: caller contract.
        let v = unsafe { crate::stdlib::num::strtoul(p, &mut end, 0) };
        if core::ptr::eq(end, p) || n == 4 {
            return 0;
        }
        parts[n] = v;
        n += 1;
        // SAFETY: `end` is inside the string.
        match unsafe { *end } {
            0 => break,
            b => {
                if b as u8 != b'.' {
                    return 0;
                }
                // SAFETY: as above.
                p = unsafe { end.add(1) };
            }
        }
    }
    let value = match n {
        1 => parts[0],
        2 => {
            if parts[1] > 0xff_ffff {
                return 0;
            }
            (parts[0] << 24) | parts[1]
        }
        3 => {
            if parts[2] > 0xffff {
                return 0;
            }
            (parts[0] << 24) | (parts[1] << 16) | parts[2]
        }
        _ => {
            if parts[3] > 0xff {
                return 0;
            }
            (parts[0] << 24) | (parts[1] << 16) | (parts[2] << 8) | parts[3]
        }
    };
    // Every part but the last must fit in a byte; the whole value in 32 bits.
    if value > 0xffff_ffff || (n >= 2 && parts[..n - 1].iter().any(|&x| x > 0xff)) {
        return 0;
    }
    // SAFETY: caller contract.
    unsafe { *out = (value as u32).to_be() };
    1
}

/// `inet_addr(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn inet_addr(s: *const c_char) -> u32 {
    let mut out = 0u32;
    // SAFETY: forwarded.
    if unsafe { inet_aton(s, &mut out) } == 1 {
        out
    } else {
        u32::MAX
    }
}

/// `inet_ntoa(3)` (per-thread buffer).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn inet_ntoa(addr: u32) -> *mut c_char {
    // SAFETY: the TCB is valid for the life of the thread.
    let buf = unsafe { &mut (*crate::thread::current()).path_buf };
    let n = format_ipv4(addr.to_ne_bytes(), &mut buf[..16]).unwrap_or(0);
    buf[n] = 0;
    buf.as_mut_ptr() as *mut c_char
}

// ---------------------------------------------------------------------
// getaddrinfo.

/// `struct addrinfo`.
#[allow(missing_docs)]
#[repr(C)]
pub struct AddrInfo {
    pub ai_flags: c_int,
    pub ai_family: c_int,
    pub ai_socktype: c_int,
    pub ai_protocol: c_int,
    pub ai_addrlen: Socklen,
    pub ai_addr: *mut c_void,
    pub ai_canonname: *mut c_char,
    pub ai_next: *mut AddrInfo,
}

/// `struct sockaddr_in`.
#[allow(missing_docs)]
#[repr(C)]
#[derive(Clone, Copy)]
pub struct SockaddrIn {
    pub sin_family: u16,
    pub sin_port: u16,
    pub sin_addr: [u8; 4],
    pub sin_zero: [u8; 8],
}

/// `struct sockaddr_in6`.
#[allow(missing_docs)]
#[repr(C)]
#[derive(Clone, Copy)]
pub struct SockaddrIn6 {
    pub sin6_family: u16,
    pub sin6_port: u16,
    pub sin6_flowinfo: u32,
    pub sin6_addr: [u8; 16],
    pub sin6_scope_id: u32,
}

#[allow(missing_docs)]
pub const AI_PASSIVE: c_int = 1;
#[allow(missing_docs)]
pub const AI_CANONNAME: c_int = 2;
#[allow(missing_docs)]
pub const AI_NUMERICHOST: c_int = 4;
#[allow(missing_docs)]
pub const AI_NUMERICSERV: c_int = 0x400;

/// `getaddrinfo` error codes.
#[allow(missing_docs)]
pub const EAI_BADFLAGS: c_int = -1;
#[allow(missing_docs)]
pub const EAI_NONAME: c_int = -2;
#[allow(missing_docs)]
pub const EAI_AGAIN: c_int = -3;
#[allow(missing_docs)]
pub const EAI_FAIL: c_int = -4;
#[allow(missing_docs)]
pub const EAI_FAMILY: c_int = -6;
#[allow(missing_docs)]
pub const EAI_SOCKTYPE: c_int = -7;
#[allow(missing_docs)]
pub const EAI_SERVICE: c_int = -8;
#[allow(missing_docs)]
pub const EAI_MEMORY: c_int = -10;
#[allow(missing_docs)]
pub const EAI_SYSTEM: c_int = -11;
#[allow(missing_docs)]
pub const EAI_OVERFLOW: c_int = -12;

/// An address found for a name.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Addr {
    /// IPv4, network order.
    V4([u8; 4]),
    /// IPv6.
    V6([u8; 16]),
}

/// A small table of well-known services.
static SERVICES: [(&[u8], u16, c_int); 12] = [
    (b"echo", 7, 0),
    (b"ftp", 21, SOCK_STREAM),
    (b"ssh", 22, SOCK_STREAM),
    (b"telnet", 23, SOCK_STREAM),
    (b"smtp", 25, SOCK_STREAM),
    (b"domain", 53, 0),
    (b"http", 80, SOCK_STREAM),
    (b"pop3", 110, SOCK_STREAM),
    (b"ntp", 123, SOCK_DGRAM),
    (b"imap", 143, SOCK_STREAM),
    (b"https", 443, SOCK_STREAM),
    (b"submission", 587, SOCK_STREAM),
];

fn resolve_service(service: &[u8], numeric_only: bool) -> Result<u16, c_int> {
    if service.is_empty() {
        return Ok(0);
    }
    if service.iter().all(u8::is_ascii_digit) {
        let v: u32 = service
            .iter()
            .try_fold(0u32, |a, &d| {
                a.checked_mul(10)?.checked_add((d - b'0') as u32)
            })
            .ok_or(EAI_SERVICE)?;
        return u16::try_from(v).map_err(|_| EAI_SERVICE);
    }
    if numeric_only {
        return Err(EAI_NONAME);
    }
    SERVICES
        .iter()
        .find(|(n, _, _)| *n == service)
        .map(|&(_, p, _)| p)
        .ok_or(EAI_SERVICE)
}

/// Looks `name` up in `/etc/hosts`, appending matches to `out`.
fn lookup_hosts(name: &[u8], out: &mut [Option<Addr>], count: &mut usize) {
    // SAFETY: NUL-terminated literals.
    let f = unsafe { crate::stdio::fopen(c"/etc/hosts".as_ptr(), c"re".as_ptr()) };
    if f.is_null() {
        return;
    }
    // SAFETY: the stream is open.
    let mut g = unsafe { crate::stdio::lock(f) };
    let mut line = [0u8; 512];
    loop {
        let mut len = 0;
        let mut eof = false;
        loop {
            match g.getc() {
                Some(b'\n') => break,
                Some(b) => {
                    if len < line.len() {
                        line[len] = b;
                        len += 1;
                    }
                }
                None => {
                    eof = true;
                    break;
                }
            }
        }
        let l = &line[..len];
        let l = match l.iter().position(|&b| b == b'#') {
            Some(p) => &l[..p],
            None => l,
        };
        let mut fields = l
            .split(|b| matches!(b, b' ' | b'\t'))
            .filter(|f| !f.is_empty());
        if let Some(addr) = fields.next() {
            let parsed = parse_ipv4(addr)
                .map(Addr::V4)
                .or_else(|| parse_ipv6(addr).map(Addr::V6));
            if let Some(a) = parsed
                && fields.any(|h| h.eq_ignore_ascii_case(name))
                && *count < out.len()
            {
                out[*count] = Some(a);
                *count += 1;
            }
        }
        if eof {
            break;
        }
    }
    drop(g);
    // SAFETY: the stream is open.
    unsafe { crate::stdio::fclose(f) };
}

/// Finds the first name for `addr` in `/etc/hosts`.
fn reverse_hosts(addr: Addr, out: &mut [u8; 256]) -> Option<usize> {
    // SAFETY: NUL-terminated literals.
    let f = unsafe { crate::stdio::fopen(c"/etc/hosts".as_ptr(), c"re".as_ptr()) };
    if f.is_null() {
        return None;
    }
    // SAFETY: the stream is open.
    let mut g = unsafe { crate::stdio::lock(f) };
    let mut line = [0u8; 512];
    let mut result = None;
    'lines: loop {
        let mut len = 0;
        let mut eof = false;
        loop {
            match g.getc() {
                Some(b'\n') => break,
                Some(b) => {
                    if len < line.len() {
                        line[len] = b;
                        len += 1;
                    }
                }
                None => {
                    eof = true;
                    break;
                }
            }
        }
        let l = &line[..len];
        let l = l.split(|&b| b == b'#').next().unwrap_or(b"");
        let mut fields = l
            .split(|b| matches!(b, b' ' | b'\t'))
            .filter(|f| !f.is_empty());
        if let Some(a) = fields.next() {
            let parsed = parse_ipv4(a)
                .map(Addr::V4)
                .or_else(|| parse_ipv6(a).map(Addr::V6));
            if parsed == Some(addr)
                && let Some(h) = fields.next()
                && h.len() < out.len()
            {
                out[..h.len()].copy_from_slice(h);
                result = Some(h.len());
                break 'lines;
            }
        }
        if eof {
            break;
        }
    }
    drop(g);
    // SAFETY: the stream is open.
    unsafe { crate::stdio::fclose(f) };
    result
}

/// `getaddrinfo(3)`.
///
/// # Safety
/// `node` and `service` must be null or NUL-terminated; `hints` null or
/// valid; `res` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getaddrinfo(
    node: *const c_char,
    service: *const c_char,
    hints: *const AddrInfo,
    res: *mut *mut AddrInfo,
) -> c_int {
    // SAFETY: caller contract.
    let (flags, family, socktype, protocol) = unsafe { hints.as_ref() }
        .map(|h| (h.ai_flags, h.ai_family, h.ai_socktype, h.ai_protocol))
        .unwrap_or((0, AF_UNSPEC, 0, 0));
    if !matches!(family, AF_UNSPEC | AF_INET | AF_INET6) {
        return EAI_FAMILY;
    }
    if !matches!(socktype, 0 | SOCK_STREAM | SOCK_DGRAM | SOCK_RAW) {
        return EAI_SOCKTYPE;
    }
    if node.is_null() && service.is_null() {
        return EAI_NONAME;
    }
    let service = if service.is_null() {
        &b""[..]
    } else {
        // SAFETY: caller contract.
        unsafe {
            core::slice::from_raw_parts(
                service as *const u8,
                crate::string::search::strlen(service as *const u8),
            )
        }
    };
    let port = match resolve_service(service, flags & AI_NUMERICSERV != 0) {
        Ok(p) => p,
        Err(e) => return e,
    };

    let mut addrs: [Option<Addr>; 16] = [None; 16];
    let mut count = 0;
    let mut canon_buf = [0u8; 256];
    let mut canon: &[u8] = b"";
    if node.is_null() {
        if flags & AI_PASSIVE != 0 {
            addrs[0] = Some(Addr::V4([0; 4]));
            addrs[1] = Some(Addr::V6([0; 16]));
        } else {
            addrs[0] = Some(Addr::V4([127, 0, 0, 1]));
            addrs[1] = Some(Addr::V6(in6addr_loopback));
        }
        count = 2;
    } else {
        // SAFETY: caller contract.
        let name = unsafe {
            core::slice::from_raw_parts(
                node as *const u8,
                crate::string::search::strlen(node as *const u8),
            )
        };
        canon = name;
        if let Some(a) = parse_ipv4(name) {
            addrs[0] = Some(Addr::V4(a));
            count = 1;
        } else if let Some(a) = parse_ipv6(name) {
            addrs[0] = Some(Addr::V6(a));
            count = 1;
        } else if flags & AI_NUMERICHOST != 0 {
            return EAI_NONAME;
        } else if name.eq_ignore_ascii_case(b"localhost") {
            addrs[0] = Some(Addr::V4([127, 0, 0, 1]));
            addrs[1] = Some(Addr::V6(in6addr_loopback));
            count = 2;
        } else {
            lookup_hosts(name, &mut addrs, &mut count);
            if count == 0 {
                match crate::resolv::lookup(
                    name,
                    family != AF_INET6,
                    family != AF_INET,
                    &mut addrs,
                    &mut canon_buf,
                ) {
                    Ok((n, clen)) => {
                        count = n;
                        if clen > 0 {
                            canon = &canon_buf[..clen];
                        }
                    }
                    Err(crate::resolv::Error::NoName) => return EAI_NONAME,
                    Err(crate::resolv::Error::Again) => return EAI_AGAIN,
                    Err(crate::resolv::Error::Fail) => return EAI_FAIL,
                }
            }
        }
    }

    // Build the list: each address × each requested socket type.
    let types: &[(c_int, c_int)] = match socktype {
        SOCK_STREAM => &[(SOCK_STREAM, IPPROTO_TCP)],
        SOCK_DGRAM => &[(SOCK_DGRAM, IPPROTO_UDP)],
        SOCK_RAW => &[(SOCK_RAW, protocol)],
        _ => &[(SOCK_STREAM, IPPROTO_TCP), (SOCK_DGRAM, IPPROTO_UDP)],
    };
    let mut head: *mut AddrInfo = ptr::null_mut();
    let mut tail: *mut *mut AddrInfo = &mut head;
    let mut any = false;
    for addr in addrs[..count].iter().flatten() {
        let fam = match addr {
            Addr::V4(_) => AF_INET,
            Addr::V6(_) => AF_INET6,
        };
        if family != AF_UNSPEC && family != fam {
            continue;
        }
        for &(st, proto) in types {
            if protocol != 0 && proto != 0 && protocol != proto {
                continue;
            }
            let size = core::mem::size_of::<AddrInfo>() + core::mem::size_of::<SockaddrIn6>();
            let p = malloc::alloc(size) as *mut AddrInfo;
            if p.is_null() {
                // SAFETY: the list so far is ours.
                unsafe { freeaddrinfo(head) };
                return EAI_MEMORY;
            }
            // SAFETY: the block holds the addrinfo followed by the sockaddr.
            unsafe {
                let sa = (p as *mut u8).add(core::mem::size_of::<AddrInfo>()) as *mut c_void;
                let addrlen = match addr {
                    Addr::V4(a) => {
                        (sa as *mut SockaddrIn).write(SockaddrIn {
                            sin_family: AF_INET as u16,
                            sin_port: port.to_be(),
                            sin_addr: *a,
                            sin_zero: [0; 8],
                        });
                        core::mem::size_of::<SockaddrIn>()
                    }
                    Addr::V6(a) => {
                        (sa as *mut SockaddrIn6).write(SockaddrIn6 {
                            sin6_family: AF_INET6 as u16,
                            sin6_port: port.to_be(),
                            sin6_flowinfo: 0,
                            sin6_addr: *a,
                            sin6_scope_id: 0,
                        });
                        core::mem::size_of::<SockaddrIn6>()
                    }
                };
                let canonname = if flags & AI_CANONNAME != 0 && !any && !canon.is_empty() {
                    let c = malloc::alloc(canon.len() + 1);
                    if !c.is_null() {
                        ptr::copy_nonoverlapping(canon.as_ptr(), c, canon.len());
                        *c.add(canon.len()) = 0;
                    }
                    c as *mut c_char
                } else {
                    ptr::null_mut()
                };
                p.write(AddrInfo {
                    ai_flags: flags,
                    ai_family: fam,
                    ai_socktype: st,
                    ai_protocol: proto,
                    ai_addrlen: addrlen as Socklen,
                    ai_addr: sa,
                    ai_canonname: canonname,
                    ai_next: ptr::null_mut(),
                });
                *tail = p;
                tail = &mut (*p).ai_next;
            }
            any = true;
        }
    }
    if !any {
        return EAI_NONAME;
    }
    // SAFETY: caller contract.
    unsafe { *res = head };
    0
}

/// `freeaddrinfo(3)`.
///
/// # Safety
/// `ai` must be null or a list from `getaddrinfo`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn freeaddrinfo(mut ai: *mut AddrInfo) {
    while !ai.is_null() {
        // SAFETY: our own blocks.
        unsafe {
            let next = (*ai).ai_next;
            malloc::dealloc((*ai).ai_canonname as *mut u8);
            malloc::dealloc(ai as *mut u8);
            ai = next;
        }
    }
}

/// `gai_strerror(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn gai_strerror(code: c_int) -> *const c_char {
    let s: &[u8] = match code {
        EAI_BADFLAGS => b"Bad value for ai_flags\0",
        EAI_NONAME => b"Name or service not known\0",
        EAI_AGAIN => b"Temporary failure in name resolution\0",
        EAI_FAIL => b"Non-recoverable failure in name resolution\0",
        EAI_FAMILY => b"ai_family not supported\0",
        EAI_SOCKTYPE => b"ai_socktype not supported\0",
        EAI_SERVICE => b"Servname not supported for ai_socktype\0",
        EAI_MEMORY => b"Memory allocation failure\0",
        EAI_SYSTEM => b"System error\0",
        EAI_OVERFLOW => b"Argument buffer overflow\0",
        _ => b"Unknown error\0",
    };
    s.as_ptr() as *const c_char
}

/// `getnameinfo(3)`: numeric forms only.
///
/// # Safety
/// `sa` must point to `salen` bytes; the buffers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getnameinfo(
    sa: *const c_void,
    salen: Socklen,
    host: *mut c_char,
    hostlen: Socklen,
    serv: *mut c_char,
    servlen: Socklen,
    flags: c_int,
) -> c_int {
    const NI_NUMERICHOST: c_int = 1;
    const NI_NOFQDN: c_int = 4;
    const NI_NAMEREQD: c_int = 8;
    if sa.is_null() || salen < 2 {
        return EAI_FAMILY;
    }
    // SAFETY: caller contract.
    let family = unsafe { *(sa as *const u16) } as c_int;
    let (port, addr) = match family {
        AF_INET if salen as usize >= core::mem::size_of::<SockaddrIn>() => {
            // SAFETY: caller contract.
            let a = unsafe { *(sa as *const SockaddrIn) };
            (u16::from_be(a.sin_port), Addr::V4(a.sin_addr))
        }
        AF_INET6 if salen as usize >= core::mem::size_of::<SockaddrIn6>() => {
            // SAFETY: caller contract.
            let a = unsafe { *(sa as *const SockaddrIn6) };
            (u16::from_be(a.sin6_port), Addr::V6(a.sin6_addr))
        }
        _ => return EAI_FAMILY,
    };
    if !host.is_null() && hostlen > 0 {
        // SAFETY: caller contract.
        let out = unsafe { core::slice::from_raw_parts_mut(host as *mut u8, hostlen as usize) };
        let mut name = [0u8; 256];
        let named = if flags & NI_NUMERICHOST != 0 {
            0
        } else {
            reverse_hosts(addr, &mut name)
                .or_else(|| crate::resolv::reverse(addr, &mut name).ok())
                .unwrap_or(0)
        };
        if named > 0 {
            let mut n = named;
            if flags & NI_NOFQDN != 0
                && let Some(dot) = name[..n].iter().position(|&b| b == b'.')
            {
                n = dot;
            }
            if n + 1 > out.len() {
                return EAI_OVERFLOW;
            }
            out[..n].copy_from_slice(&name[..n]);
            out[n] = 0;
        } else {
            if flags & NI_NAMEREQD != 0 {
                return EAI_NONAME;
            }
            let formatted = match addr {
                Addr::V4(a) => format_ipv4(a, out),
                Addr::V6(a) => format_ipv6(a, out),
            };
            match formatted {
                Some(n) => out[n] = 0,
                None => return EAI_OVERFLOW,
            }
        }
    }
    if !serv.is_null() && servlen > 0 {
        // SAFETY: caller contract.
        let out = unsafe { core::slice::from_raw_parts_mut(serv as *mut u8, servlen as usize) };
        let mut w = crate::fmt::SliceWriter::new(out);
        let _ = core::fmt::write(&mut w, format_args!("{port}"));
        let n = w.len();
        if n + 1 > out.len() || (port >= 10 && n < 2) {
            return EAI_OVERFLOW;
        }
        out[n] = 0;
    }
    0
}

/// `struct hostent`.
#[allow(missing_docs)]
#[repr(C)]
pub struct Hostent {
    pub h_name: *mut c_char,
    pub h_aliases: *mut *mut c_char,
    pub h_addrtype: c_int,
    pub h_length: c_int,
    pub h_addr_list: *mut *mut c_char,
}

struct HostentStatic {
    ent: Hostent,
    name: [u8; 256],
    aliases: [*mut c_char; 1],
    addrs: [[u8; 16]; 8],
    list: [*mut c_char; 9],
}
// SAFETY: guarded by the mutex.
unsafe impl Send for HostentStatic {}
static HOSTENT: crate::sync::Mutex<HostentStatic> = crate::sync::Mutex::new(HostentStatic {
    ent: Hostent {
        h_name: ptr::null_mut(),
        h_aliases: ptr::null_mut(),
        h_addrtype: 0,
        h_length: 0,
        h_addr_list: ptr::null_mut(),
    },
    name: [0; 256],
    aliases: [ptr::null_mut(); 1],
    addrs: [[0; 16]; 8],
    list: [ptr::null_mut(); 9],
});

/// `h_errno`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut h_errno: c_int = 0;

/// Fills the static `hostent` from an address list.
///
/// # Safety
/// `name` must be NUL-terminated; `res` a list from `getaddrinfo`.
unsafe fn fill_hostent(name: *const c_char, family: c_int, res: *mut AddrInfo) -> *mut Hostent {
    let mut s = HOSTENT.lock();
    let s = &mut *s;
    // SAFETY: caller contract.
    let n = unsafe { crate::string::search::strlen(name as *const u8) }.min(255);
    // SAFETY: as above.
    unsafe { ptr::copy_nonoverlapping(name as *const u8, s.name.as_mut_ptr(), n) };
    s.name[n] = 0;
    let mut count = 0;
    let mut p = res;
    while !p.is_null() && count < 8 {
        // SAFETY: entries from getaddrinfo.
        unsafe {
            if (*p).ai_family == family {
                if family == AF_INET {
                    s.addrs[count][..4]
                        .copy_from_slice(&(*((*p).ai_addr as *const SockaddrIn)).sin_addr);
                } else {
                    s.addrs[count] = (*((*p).ai_addr as *const SockaddrIn6)).sin6_addr;
                }
                count += 1;
            }
            p = (*p).ai_next;
        }
    }
    for i in 0..count {
        s.list[i] = s.addrs[i].as_mut_ptr() as *mut c_char;
    }
    s.list[count] = ptr::null_mut();
    s.aliases[0] = ptr::null_mut();
    s.ent = Hostent {
        h_name: s.name.as_mut_ptr() as *mut c_char,
        h_aliases: s.aliases.as_mut_ptr(),
        h_addrtype: family,
        h_length: if family == AF_INET { 4 } else { 16 },
        h_addr_list: s.list.as_mut_ptr(),
    };
    &mut s.ent
}

/// Maps a `getaddrinfo` error to `h_errno`.
fn set_h_errno(code: c_int) {
    let v = match code {
        EAI_AGAIN => 2,  // TRY_AGAIN
        EAI_FAIL => 3,   // NO_RECOVERY
        EAI_NONAME => 1, // HOST_NOT_FOUND
        _ => 3,
    };
    // SAFETY: single global.
    unsafe { h_errno = v };
}

/// `gethostbyname2(3)`.
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn gethostbyname2(name: *const c_char, family: c_int) -> *mut Hostent {
    if family != AF_INET && family != AF_INET6 {
        set_h_errno(EAI_FAIL);
        return ptr::null_mut();
    }
    let hints = AddrInfo {
        ai_flags: AI_CANONNAME,
        ai_family: family,
        ai_socktype: SOCK_STREAM,
        ai_protocol: 0,
        ai_addrlen: 0,
        ai_addr: ptr::null_mut(),
        ai_canonname: ptr::null_mut(),
        ai_next: ptr::null_mut(),
    };
    let mut res: *mut AddrInfo = ptr::null_mut();
    // SAFETY: forwarded.
    let r = unsafe { getaddrinfo(name, ptr::null(), &hints, &mut res) };
    if r != 0 {
        set_h_errno(r);
        return ptr::null_mut();
    }
    // SAFETY: the list is ours; the canonical name is NUL-terminated.
    let canon = unsafe { (*res).ai_canonname };
    // SAFETY: forwarded.
    let ent = unsafe { fill_hostent(if canon.is_null() { name } else { canon }, family, res) };
    // SAFETY: the list is ours.
    unsafe { freeaddrinfo(res) };
    ent
}

/// `gethostbyname(3)`.
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn gethostbyname(name: *const c_char) -> *mut Hostent {
    // SAFETY: forwarded.
    unsafe { gethostbyname2(name, AF_INET) }
}

/// `gethostbyaddr(3)`.
///
/// # Safety
/// `addr` must be valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn gethostbyaddr(
    addr: *const c_void,
    len: Socklen,
    family: c_int,
) -> *mut Hostent {
    let a = match (family, len) {
        (AF_INET, 4) => {
            // SAFETY: caller contract.
            Addr::V4(unsafe { *(addr as *const [u8; 4]) })
        }
        (AF_INET6, 16) => {
            // SAFETY: caller contract.
            Addr::V6(unsafe { *(addr as *const [u8; 16]) })
        }
        _ => {
            set_h_errno(EAI_FAIL);
            return ptr::null_mut();
        }
    };
    let mut name = [0u8; 256];
    let n = match reverse_hosts(a, &mut name).or_else(|| crate::resolv::reverse(a, &mut name).ok())
    {
        Some(n) => n,
        None => {
            set_h_errno(EAI_NONAME);
            return ptr::null_mut();
        }
    };
    let mut s = HOSTENT.lock();
    let s = &mut *s;
    s.name[..n].copy_from_slice(&name[..n]);
    s.name[n] = 0;
    s.addrs[0] = [0; 16];
    match a {
        Addr::V4(v) => s.addrs[0][..4].copy_from_slice(&v),
        Addr::V6(v) => s.addrs[0] = v,
    }
    s.list[0] = s.addrs[0].as_mut_ptr() as *mut c_char;
    s.list[1] = ptr::null_mut();
    s.aliases[0] = ptr::null_mut();
    s.ent = Hostent {
        h_name: s.name.as_mut_ptr() as *mut c_char,
        h_aliases: s.aliases.as_mut_ptr(),
        h_addrtype: family,
        h_length: len as c_int,
        h_addr_list: s.list.as_mut_ptr(),
    };
    &mut s.ent
}

/// `hstrerror(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn hstrerror(err: c_int) -> *const c_char {
    match err {
        0 => c"Resolver Error 0 (no error)".as_ptr(),
        1 => c"Unknown host".as_ptr(),
        2 => c"Host name lookup failure".as_ptr(),
        3 => c"Unknown server error".as_ptr(),
        4 => c"No address associated with name".as_ptr(),
        _ => c"Unknown resolver error".as_ptr(),
    }
}

/// Timespec is used by callers of `select`-style APIs in `poll.rs`.
#[allow(dead_code)]
fn _ts(_: Timespec) {}

#[cfg(test)]
mod tests {
    use super::*;

    fn v4(s: &str) -> Option<[u8; 4]> {
        parse_ipv4(s.as_bytes())
    }
    fn v6(s: &str) -> Option<String> {
        parse_ipv6(s.as_bytes()).map(|a| {
            let mut buf = [0u8; 64];
            let n = format_ipv6(a, &mut buf).unwrap();
            String::from_utf8(buf[..n].to_vec()).unwrap()
        })
    }

    #[test]
    fn ipv4_text() {
        assert_eq!(v4("127.0.0.1"), Some([127, 0, 0, 1]));
        assert_eq!(v4("255.255.255.255"), Some([255; 4]));
        assert_eq!(v4("256.0.0.1"), None);
        assert_eq!(v4("1.2.3"), None);
        assert_eq!(v4("1.2.3.4.5"), None);
        assert_eq!(v4("01.2.3.4"), None);
        assert_eq!(v4("1.2.3.4 "), None);
        assert_eq!(v4(""), None);
        let mut buf = [0u8; 16];
        let n = format_ipv4([10, 0, 0, 255], &mut buf).unwrap();
        assert_eq!(&buf[..n], b"10.0.0.255");
        assert!(format_ipv4([10, 0, 0, 255], &mut buf[..8]).is_none());
    }

    #[test]
    fn ipv6_text() {
        assert_eq!(v6("::1").as_deref(), Some("::1"));
        assert_eq!(v6("::").as_deref(), Some("::"));
        assert_eq!(v6("2001:db8::1").as_deref(), Some("2001:db8::1"));
        assert_eq!(
            v6("2001:0DB8:0000:0000:0000:0000:0000:0001").as_deref(),
            Some("2001:db8::1")
        );
        assert_eq!(v6("fe80::1%").is_none(), true);
        assert_eq!(v6("1:2:3:4:5:6:7:8").as_deref(), Some("1:2:3:4:5:6:7:8"));
        assert_eq!(v6("1::2:0:0:3").as_deref(), Some("1::2:0:0:3"));
        assert_eq!(v6("1:0:0:2::3").as_deref(), Some("1:0:0:2::3"));
        assert_eq!(
            v6("::ffff:192.168.1.1").as_deref(),
            Some("::ffff:192.168.1.1")
        );
        assert_eq!(v6("64:ff9b::1.2.3.4").as_deref(), Some("64:ff9b::102:304"));
        assert_eq!(v6("1:2:3:4:5:6:7:8:9"), None);
        assert_eq!(v6(":1"), None);
        assert_eq!(v6("1:"), None);
        assert_eq!(v6("1::2::3"), None);
        assert_eq!(v6("12345::"), None);
        assert_eq!(v6("g::"), None);
        assert_eq!(v6("1:2:3:4:5:6:7::").as_deref(), Some("1:2:3:4:5:6:7:0"));
        assert_eq!(v6("::2:3:4:5:6:7:8").as_deref(), Some("0:2:3:4:5:6:7:8"));
        assert_eq!(v6("0:0:0:0:0:0:0:1").as_deref(), Some("::1"));
        assert_eq!(v6("1:0:0:0:0:0:0:0").as_deref(), Some("1::"));
    }

    #[test]
    fn aton_and_resolution() {
        let mut out = 0u32;
        // SAFETY: NUL-terminated literals and a valid out-pointer.
        unsafe {
            // `s_addr` holds the address in network byte order.
            assert_eq!(inet_aton(c"127.0.0.1".as_ptr(), &mut out), 1);
            assert_eq!(out.to_ne_bytes(), [127, 0, 0, 1]);
            assert_eq!(inet_aton(c"0x7f000001".as_ptr(), &mut out), 1);
            assert_eq!(out.to_ne_bytes(), [127, 0, 0, 1]);
            assert_eq!(inet_aton(c"127.1".as_ptr(), &mut out), 1);
            assert_eq!(out.to_ne_bytes(), [127, 0, 0, 1]);
            assert_eq!(inet_aton(c"1.2.3.256".as_ptr(), &mut out), 0);
            assert_eq!(inet_aton(c"junk".as_ptr(), &mut out), 0);
            assert_eq!(inet_addr(c"junk".as_ptr()), u32::MAX);
            assert_eq!(
                std::ffi::CStr::from_ptr(inet_ntoa(u32::from_ne_bytes([1, 2, 3, 4]))).to_bytes(),
                b"1.2.3.4"
            );
        }
        assert_eq!(resolve_service(b"80", false), Ok(80));
        assert_eq!(resolve_service(b"http", false), Ok(80));
        assert_eq!(resolve_service(b"http", true), Err(EAI_NONAME));
        assert_eq!(resolve_service(b"70000", false), Err(EAI_SERVICE));
        assert_eq!(resolve_service(b"nope", false), Err(EAI_SERVICE));
        let hints = AddrInfo {
            ai_flags: 0,
            ai_family: AF_UNSPEC,
            ai_socktype: SOCK_STREAM,
            ai_protocol: 0,
            ai_addrlen: 0,
            ai_addr: ptr::null_mut(),
            ai_canonname: ptr::null_mut(),
            ai_next: ptr::null_mut(),
        };
        let mut res: *mut AddrInfo = ptr::null_mut();
        // SAFETY: valid inputs.
        unsafe {
            assert_eq!(
                getaddrinfo(c"localhost".as_ptr(), c"http".as_ptr(), &hints, &mut res),
                0
            );
            let first = &*res;
            assert_eq!(first.ai_family, AF_INET);
            assert_eq!(
                (*(first.ai_addr as *const SockaddrIn)).sin_port,
                80u16.to_be()
            );
            let second = &*first.ai_next;
            assert_eq!(second.ai_family, AF_INET6);
            assert!(second.ai_next.is_null());
            freeaddrinfo(res);
            assert_eq!(
                getaddrinfo(c"10.1.2.3".as_ptr(), ptr::null(), ptr::null(), &mut res),
                0
            );
            assert_eq!((*res).ai_socktype, SOCK_STREAM);
            assert_eq!((*(*res).ai_next).ai_socktype, SOCK_DGRAM);
            let mut host = [0 as c_char; 64];
            let mut serv = [0 as c_char; 16];
            assert_eq!(
                getnameinfo(
                    (*res).ai_addr,
                    (*res).ai_addrlen,
                    host.as_mut_ptr(),
                    64,
                    serv.as_mut_ptr(),
                    16,
                    0
                ),
                0
            );
            assert_eq!(
                std::ffi::CStr::from_ptr(host.as_ptr()).to_bytes(),
                b"10.1.2.3"
            );
            assert_eq!(std::ffi::CStr::from_ptr(serv.as_ptr()).to_bytes(), b"0");
            freeaddrinfo(res);
            assert_eq!(
                getaddrinfo(
                    c"no.such.host.invalid".as_ptr(),
                    ptr::null(),
                    ptr::null(),
                    &mut res
                ),
                EAI_NONAME
            );
            let numeric = AddrInfo {
                ai_flags: AI_NUMERICHOST,
                ..hints
            };
            assert_eq!(
                getaddrinfo(c"localhost".as_ptr(), ptr::null(), &numeric, &mut res),
                EAI_NONAME
            );
            let h = gethostbyname(c"localhost".as_ptr());
            assert!(!h.is_null());
            assert_eq!((*h).h_length, 4);
            assert_eq!(*((*(*h).h_addr_list) as *const [u8; 4]), [127, 0, 0, 1]);
        }
    }
}
