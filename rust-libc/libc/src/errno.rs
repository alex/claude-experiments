//! `errno` and the error number constants.
//!
//! Internally the library never touches the C `errno`; syscall wrappers
//! return [`Errno`] values and the exported C entry points convert them
//! with [`Errno::set`] right before returning `-1`.

use core::ffi::c_int;

/// A Linux error number.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Errno(pub c_int);

macro_rules! errnos {
    ($($name:ident = $num:expr, $desc:expr;)*) => {
        #[allow(missing_docs)]
        impl Errno {
            $(pub const $name: Errno = Errno($num);)*
        }

        /// Returns the `strerror` text for an error number, if it is
        /// known, as a NUL-terminated string (the NUL is included in the
        /// slice so the pointer can be handed to C directly).
        pub fn description_cstr(num: c_int) -> Option<&'static str> {
            match num {
                $($num => Some(concat!($desc, "\0")),)*
                _ => None,
            }
        }
    };
}

errnos! {
    EPERM = 1, "Operation not permitted";
    ENOENT = 2, "No such file or directory";
    ESRCH = 3, "No such process";
    EINTR = 4, "Interrupted system call";
    EIO = 5, "Input/output error";
    ENXIO = 6, "No such device or address";
    E2BIG = 7, "Argument list too long";
    ENOEXEC = 8, "Exec format error";
    EBADF = 9, "Bad file descriptor";
    ECHILD = 10, "No child processes";
    EAGAIN = 11, "Resource temporarily unavailable";
    ENOMEM = 12, "Cannot allocate memory";
    EACCES = 13, "Permission denied";
    EFAULT = 14, "Bad address";
    ENOTBLK = 15, "Block device required";
    EBUSY = 16, "Device or resource busy";
    EEXIST = 17, "File exists";
    EXDEV = 18, "Invalid cross-device link";
    ENODEV = 19, "No such device";
    ENOTDIR = 20, "Not a directory";
    EISDIR = 21, "Is a directory";
    EINVAL = 22, "Invalid argument";
    ENFILE = 23, "Too many open files in system";
    EMFILE = 24, "Too many open files";
    ENOTTY = 25, "Inappropriate ioctl for device";
    ETXTBSY = 26, "Text file busy";
    EFBIG = 27, "File too large";
    ENOSPC = 28, "No space left on device";
    ESPIPE = 29, "Illegal seek";
    EROFS = 30, "Read-only file system";
    EMLINK = 31, "Too many links";
    EPIPE = 32, "Broken pipe";
    EDOM = 33, "Numerical argument out of domain";
    ERANGE = 34, "Numerical result out of range";
    EDEADLK = 35, "Resource deadlock avoided";
    ENAMETOOLONG = 36, "File name too long";
    ENOLCK = 37, "No locks available";
    ENOSYS = 38, "Function not implemented";
    ENOTEMPTY = 39, "Directory not empty";
    ELOOP = 40, "Too many levels of symbolic links";
    ENOMSG = 42, "No message of desired type";
    EIDRM = 43, "Identifier removed";
    ECHRNG = 44, "Channel number out of range";
    EL2NSYNC = 45, "Level 2 not synchronized";
    EL3HLT = 46, "Level 3 halted";
    EL3RST = 47, "Level 3 reset";
    ELNRNG = 48, "Link number out of range";
    EUNATCH = 49, "Protocol driver not attached";
    ENOCSI = 50, "No CSI structure available";
    EL2HLT = 51, "Level 2 halted";
    EBADE = 52, "Invalid exchange";
    EBADR = 53, "Invalid request descriptor";
    EXFULL = 54, "Exchange full";
    ENOANO = 55, "No anode";
    EBADRQC = 56, "Invalid request code";
    EBADSLT = 57, "Invalid slot";
    EBFONT = 59, "Bad font file format";
    ENOSTR = 60, "Device not a stream";
    ENODATA = 61, "No data available";
    ETIME = 62, "Timer expired";
    ENOSR = 63, "Out of streams resources";
    ENONET = 64, "Machine is not on the network";
    ENOPKG = 65, "Package not installed";
    EREMOTE = 66, "Object is remote";
    ENOLINK = 67, "Link has been severed";
    EADV = 68, "Advertise error";
    ESRMNT = 69, "Srmount error";
    ECOMM = 70, "Communication error on send";
    EPROTO = 71, "Protocol error";
    EMULTIHOP = 72, "Multihop attempted";
    EDOTDOT = 73, "RFS specific error";
    EBADMSG = 74, "Bad message";
    EOVERFLOW = 75, "Value too large for defined data type";
    ENOTUNIQ = 76, "Name not unique on network";
    EBADFD = 77, "File descriptor in bad state";
    EREMCHG = 78, "Remote address changed";
    ELIBACC = 79, "Can not access a needed shared library";
    ELIBBAD = 80, "Accessing a corrupted shared library";
    ELIBSCN = 81, ".lib section in a.out corrupted";
    ELIBMAX = 82, "Attempting to link in too many shared libraries";
    ELIBEXEC = 83, "Cannot exec a shared library directly";
    EILSEQ = 84, "Invalid or incomplete multibyte or wide character";
    ERESTART = 85, "Interrupted system call should be restarted";
    ESTRPIPE = 86, "Streams pipe error";
    EUSERS = 87, "Too many users";
    ENOTSOCK = 88, "Socket operation on non-socket";
    EDESTADDRREQ = 89, "Destination address required";
    EMSGSIZE = 90, "Message too long";
    EPROTOTYPE = 91, "Protocol wrong type for socket";
    ENOPROTOOPT = 92, "Protocol not available";
    EPROTONOSUPPORT = 93, "Protocol not supported";
    ESOCKTNOSUPPORT = 94, "Socket type not supported";
    EOPNOTSUPP = 95, "Operation not supported";
    EPFNOSUPPORT = 96, "Protocol family not supported";
    EAFNOSUPPORT = 97, "Address family not supported by protocol";
    EADDRINUSE = 98, "Address already in use";
    EADDRNOTAVAIL = 99, "Cannot assign requested address";
    ENETDOWN = 100, "Network is down";
    ENETUNREACH = 101, "Network is unreachable";
    ENETRESET = 102, "Network dropped connection on reset";
    ECONNABORTED = 103, "Software caused connection abort";
    ECONNRESET = 104, "Connection reset by peer";
    ENOBUFS = 105, "No buffer space available";
    EISCONN = 106, "Transport endpoint is already connected";
    ENOTCONN = 107, "Transport endpoint is not connected";
    ESHUTDOWN = 108, "Cannot send after transport endpoint shutdown";
    ETOOMANYREFS = 109, "Too many references: cannot splice";
    ETIMEDOUT = 110, "Connection timed out";
    ECONNREFUSED = 111, "Connection refused";
    EHOSTDOWN = 112, "Host is down";
    EHOSTUNREACH = 113, "No route to host";
    EALREADY = 114, "Operation already in progress";
    EINPROGRESS = 115, "Operation now in progress";
    ESTALE = 116, "Stale file handle";
    EUCLEAN = 117, "Structure needs cleaning";
    ENOTNAM = 118, "Not a XENIX named type file";
    ENAVAIL = 119, "No XENIX semaphores available";
    EISNAM = 120, "Is a named type file";
    EREMOTEIO = 121, "Remote I/O error";
    EDQUOT = 122, "Disk quota exceeded";
    ENOMEDIUM = 123, "No medium found";
    EMEDIUMTYPE = 124, "Wrong medium type";
    ECANCELED = 125, "Operation canceled";
    ENOKEY = 126, "Required key not available";
    EKEYEXPIRED = 127, "Key has expired";
    EKEYREVOKED = 128, "Key has been revoked";
    EKEYREJECTED = 129, "Key was rejected by service";
    EOWNERDEAD = 130, "Owner died";
    ENOTRECOVERABLE = 131, "State not recoverable";
    ERFKILL = 132, "Operation not possible due to RF-kill";
    EHWPOISON = 133, "Memory page has hardware error";
}

/// Returns the `strerror` text for an error number, if it is known.
pub fn description(num: c_int) -> Option<&'static str> {
    description_cstr(num).map(|s| &s[..s.len() - 1])
}

impl Errno {
    /// Stores this error number in the calling thread's `errno`.
    #[inline]
    pub fn set(self) {
        // SAFETY: the current thread's TCB is always valid.
        unsafe { (*crate::thread::current()).errno = self.0 }
    }

    /// Reads the calling thread's `errno`.
    #[inline]
    pub fn get() -> Errno {
        // SAFETY: the current thread's TCB is always valid.
        Errno(unsafe { (*crate::thread::current()).errno })
    }
}

/// Returns the address of the calling thread's `errno`.
///
/// C code accesses `errno` as `(*__errno_location())`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __errno_location() -> *mut c_int {
    // SAFETY: the current thread's TCB is always valid; the pointer is
    // valid for as long as the thread lives.
    unsafe { &raw mut (*crate::thread::current()).errno }
}

/// Helper trait to turn a syscall [`Result`](crate::sys::Result) into the
/// C convention of `-1` plus `errno`.
pub trait CReturn {
    /// The C return type.
    type Out;
    /// Converts the result, setting `errno` on error.
    fn c_ret(self) -> Self::Out;
}

/// Like [`CReturn`] for arbitrary return types: yields `fail` (and sets
/// `errno`) on error.
pub trait CReturnOr<T> {
    /// Converts the result, setting `errno` on error.
    fn c_ret_or(self, fail: T) -> T;
}

impl<T> CReturnOr<T> for crate::sys::Result<T> {
    #[inline]
    fn c_ret_or(self, fail: T) -> T {
        match self {
            Ok(v) => v,
            Err(e) => {
                e.set();
                fail
            }
        }
    }
}

impl CReturn for crate::sys::Result<()> {
    type Out = c_int;
    #[inline]
    fn c_ret(self) -> c_int {
        match self {
            Ok(()) => 0,
            Err(e) => {
                e.set();
                -1
            }
        }
    }
}

impl CReturn for crate::sys::Result<usize> {
    type Out = isize;
    #[inline]
    fn c_ret(self) -> isize {
        match self {
            Ok(v) => v as isize,
            Err(e) => {
                e.set();
                -1
            }
        }
    }
}

impl CReturn for crate::sys::Result<c_int> {
    type Out = c_int;
    #[inline]
    fn c_ret(self) -> c_int {
        match self {
            Ok(v) => v,
            Err(e) => {
                e.set();
                -1
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn descriptions() {
        assert_eq!(description(2), Some("No such file or directory"));
        assert_eq!(description(0), None);
        assert_eq!(description(134), None);
        assert_eq!(Errno::ENOENT, Errno(2));
    }

    #[test]
    fn set_get_roundtrip() {
        Errno::EBADF.set();
        assert_eq!(Errno::get(), Errno::EBADF);
        // SAFETY: __errno_location returns a valid pointer.
        unsafe { *__errno_location() = 5 };
        assert_eq!(Errno::get(), Errno::EIO);
    }
}
