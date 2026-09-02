//! `<syslog.h>`: messages go to `/dev/log` over a datagram socket.

use crate::c_char;
use crate::stdio::printf::Sink;
use crate::sync::Mutex;
use crate::sys;
use core::ffi::c_int;
use core::ptr;

#[allow(missing_docs)]
pub const LOG_PID: c_int = 1;
#[allow(missing_docs)]
pub const LOG_CONS: c_int = 2;
#[allow(missing_docs)]
pub const LOG_NDELAY: c_int = 8;
#[allow(missing_docs)]
pub const LOG_PERROR: c_int = 0x20;
#[allow(missing_docs)]
pub const LOG_USER: c_int = 1 << 3;

struct State {
    ident: [u8; 64],
    ident_len: usize,
    options: c_int,
    facility: c_int,
    mask: c_int,
    fd: c_int,
}

static STATE: Mutex<State> = Mutex::new(State {
    ident: [0; 64],
    ident_len: 0,
    options: 0,
    facility: LOG_USER,
    mask: 0xff,
    fd: -1,
});

fn connect_log(st: &mut State) {
    if st.fd >= 0 {
        return;
    }
    // SAFETY: no memory beyond the address structure.
    unsafe {
        let fd = crate::socket::socket(
            crate::socket::AF_UNIX,
            crate::socket::SOCK_DGRAM | sys::O_CLOEXEC,
            0,
        );
        if fd < 0 {
            return;
        }
        #[repr(C)]
        struct SockaddrUn {
            family: u16,
            path: [u8; 108],
        }
        let mut addr = SockaddrUn {
            family: crate::socket::AF_UNIX as u16,
            path: [0; 108],
        };
        addr.path[..8].copy_from_slice(b"/dev/log");
        if crate::socket::connect(
            fd,
            &addr as *const SockaddrUn as *const core::ffi::c_void,
            2 + 9,
        ) < 0
        {
            let _ = sys::close(fd);
            return;
        }
        st.fd = fd;
    }
}

/// `openlog(3)`.
///
/// # Safety
/// `ident` must be null or NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn openlog(ident: *const c_char, options: c_int, facility: c_int) {
    let mut st = STATE.lock();
    st.ident_len = 0;
    if !ident.is_null() {
        // SAFETY: caller contract.
        let s = unsafe {
            core::slice::from_raw_parts(
                ident as *const u8,
                crate::string::search::strlen(ident as *const u8),
            )
        };
        let n = s.len().min(63);
        st.ident[..n].copy_from_slice(&s[..n]);
        st.ident_len = n;
    }
    st.options = options;
    st.facility = facility;
    if options & LOG_NDELAY != 0 {
        connect_log(&mut st);
    }
}

/// `closelog(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn closelog() {
    let mut st = STATE.lock();
    if st.fd >= 0 {
        let _ = sys::close(st.fd);
        st.fd = -1;
    }
}

/// `setlogmask(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn setlogmask(mask: c_int) -> c_int {
    let mut st = STATE.lock();
    let old = st.mask;
    if mask != 0 {
        st.mask = mask;
    }
    old
}

/// A sink collecting the message in a fixed buffer.
struct Buf {
    data: [u8; 1024],
    len: usize,
}

impl Sink for Buf {
    fn write(&mut self, d: &[u8]) -> bool {
        let n = d.len().min(self.data.len() - self.len);
        self.data[self.len..self.len + n].copy_from_slice(&d[..n]);
        self.len += n;
        true
    }
}

/// `vsyslog(3)`.
///
/// # Safety
/// `fmt` must be NUL-terminated with matching arguments.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vsyslog(
    priority: c_int,
    fmt: *const c_char,
    ap: *mut crate::arch::va::VaList,
) {
    let mut st = STATE.lock();
    let level = priority & 7;
    if st.mask & (1 << level) == 0 {
        return;
    }
    let facility = if priority & !7 != 0 {
        priority & !7
    } else {
        st.facility
    };
    let mut buf = Buf {
        data: [0; 1024],
        len: 0,
    };
    // Header: "<pri>ident[pid]: ".
    let mut head = [0u8; 96];
    let mut w = crate::fmt::SliceWriter::new(&mut head);
    let _ = core::fmt::write(&mut w, format_args!("<{}>", facility | level));
    let hl = w.len();
    buf.write(&head[..hl]);
    let ident = st.ident[..st.ident_len].to_owned_array();
    buf.write(&ident.0[..ident.1]);
    if st.options & LOG_PID != 0 {
        let mut pid = [0u8; 16];
        let mut w = crate::fmt::SliceWriter::new(&mut pid);
        let _ = core::fmt::write(&mut w, format_args!("[{}]", sys::getpid()));
        let n = w.len();
        buf.write(&pid[..n]);
    }
    if st.ident_len > 0 || st.options & LOG_PID != 0 {
        buf.write(b": ");
    }
    let body_start = buf.len;
    // SAFETY: caller contract.
    unsafe { crate::stdio::printf::format(&mut buf, fmt as *const u8, &mut *ap) };
    if st.options & LOG_PERROR != 0 {
        let _ = sys::write_all(2, &buf.data[body_start..buf.len]);
        let _ = sys::write_all(2, b"\n");
    }
    connect_log(&mut st);
    if st.fd >= 0 {
        // SAFETY: the buffer is valid.
        let r = unsafe { sys::write(st.fd, buf.data.as_ptr(), buf.len) };
        if r.is_err() {
            let _ = sys::close(st.fd);
            st.fd = -1;
        }
    }
}

trait ToOwnedArray {
    fn to_owned_array(&self) -> ([u8; 64], usize);
}
impl ToOwnedArray for [u8] {
    fn to_owned_array(&self) -> ([u8; 64], usize) {
        let mut a = [0u8; 64];
        let n = self.len().min(64);
        a[..n].copy_from_slice(&self[..n]);
        (a, n)
    }
}

#[cfg(not(test))]
mod stubs {
    use crate::arch::va::variadic_stub;
    variadic_stub!(syslog, 2, super::vsyslog);
}

/// Keeps `ptr` referenced for header-facing code.
#[allow(dead_code)]
fn _p() -> *const u8 {
    ptr::null()
}
