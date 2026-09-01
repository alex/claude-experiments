//! `<dirent.h>` over `getdents64`.

use crate::c_char;
use crate::errno::Errno;
use crate::malloc;
use crate::sys::{self, AT_FDCWD, O_CLOEXEC, O_DIRECTORY, O_RDONLY};
use core::ffi::{c_int, c_long, c_void};
use core::ptr;

/// `struct dirent` (the kernel's `linux_dirent64`).
#[allow(missing_docs)]
#[repr(C)]
pub struct Dirent {
    /// Inode number.
    pub d_ino: u64,
    /// Opaque offset for `seekdir`.
    pub d_off: i64,
    /// Length of this record.
    pub d_reclen: u16,
    /// `DT_*` type.
    pub d_type: u8,
    /// NUL-terminated name.
    pub d_name: [c_char; 256],
}

const BUF_SIZE: usize = 8192;

/// `DIR`.
#[repr(C)]
pub struct Dir {
    fd: c_int,
    lock: crate::sync::RawMutex,
    pos: usize,
    len: usize,
    tell: i64,
    buf: [u8; BUF_SIZE],
}

/// `fdopendir(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fdopendir(fd: c_int) -> *mut Dir {
    let mut st = crate::fs::Stat::default();
    // SAFETY: valid pointer.
    if unsafe { crate::fs::fstat(fd, &mut st) } < 0 {
        return ptr::null_mut();
    }
    if st.st_mode & 0o170000 != 0o040000 {
        Errno::ENOTDIR.set();
        return ptr::null_mut();
    }
    let d = malloc::alloc(core::mem::size_of::<Dir>()) as *mut Dir;
    if d.is_null() {
        return d;
    }
    // SAFETY: fresh block of the right size.
    unsafe {
        ptr::addr_of_mut!((*d).fd).write(fd);
        ptr::addr_of_mut!((*d).lock).write(crate::sync::RawMutex::new());
        ptr::addr_of_mut!((*d).pos).write(0);
        ptr::addr_of_mut!((*d).len).write(0);
        ptr::addr_of_mut!((*d).tell).write(0);
    }
    d
}

/// `opendir(3)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn opendir(path: *const c_char) -> *mut Dir {
    // SAFETY: forwarded.
    let fd = match unsafe {
        sys::openat(
            AT_FDCWD,
            path as *const u8,
            O_RDONLY | O_DIRECTORY | O_CLOEXEC,
            0,
        )
    } {
        Ok(fd) => fd,
        Err(e) => {
            e.set();
            return ptr::null_mut();
        }
    };
    let d = fdopendir(fd);
    if d.is_null() {
        let _ = sys::close(fd);
    }
    d
}

/// `closedir(3)`.
///
/// # Safety
/// `d` must be an open directory stream, not used afterwards.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn closedir(d: *mut Dir) -> c_int {
    // SAFETY: caller contract.
    let fd = unsafe { (*d).fd };
    // SAFETY: our own block.
    unsafe { malloc::dealloc(d as *mut u8) };
    crate::errno::CReturn::c_ret(sys::close(fd))
}

/// `dirfd(3)`.
///
/// # Safety
/// `d` must be an open directory stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn dirfd(d: *mut Dir) -> c_int {
    // SAFETY: caller contract.
    unsafe { (*d).fd }
}

/// `readdir(3)`. The returned entry lives in the stream's buffer until
/// the next call.
///
/// # Safety
/// `d` must be an open directory stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn readdir(d: *mut Dir) -> *mut Dirent {
    // SAFETY: caller contract; the lock serialises access.
    unsafe {
        (*d).lock.lock();
        let r = readdir_locked(&mut *d);
        (*d).lock.unlock();
        r
    }
}

fn readdir_locked(d: &mut Dir) -> *mut Dirent {
    if d.pos >= d.len {
        // SAFETY: the buffer is valid.
        let r = unsafe {
            crate::arch::syscall3(
                crate::arch::nr::GETDENTS64,
                d.fd as usize,
                d.buf.as_mut_ptr() as usize,
                BUF_SIZE,
            )
        };
        match sys::check(r) {
            Ok(0) => return ptr::null_mut(),
            Ok(n) => {
                d.len = n;
                d.pos = 0;
            }
            Err(e) => {
                e.set();
                return ptr::null_mut();
            }
        }
    }
    // SAFETY: the kernel wrote a valid record at `pos`.
    let ent = unsafe { d.buf.as_mut_ptr().add(d.pos) as *mut Dirent };
    // SAFETY: as above.
    unsafe {
        d.pos += (*ent).d_reclen as usize;
        d.tell = (*ent).d_off;
    }
    ent
}

/// `readdir_r(3)` (deprecated but still used).
///
/// # Safety
/// All pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn readdir_r(
    d: *mut Dir,
    entry: *mut Dirent,
    result: *mut *mut Dirent,
) -> c_int {
    Errno(0).set();
    // SAFETY: forwarded.
    let e = unsafe { readdir(d) };
    if e.is_null() {
        // SAFETY: caller contract.
        unsafe { *result = ptr::null_mut() };
        return Errno::get().0;
    }
    // SAFETY: the record has `d_reclen` bytes; `entry` is a full dirent.
    unsafe {
        ptr::copy_nonoverlapping(e as *const u8, entry as *mut u8, (*e).d_reclen as usize);
        *result = entry;
    }
    0
}

/// `rewinddir(3)`.
///
/// # Safety
/// `d` must be an open directory stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn rewinddir(d: *mut Dir) {
    // SAFETY: caller contract.
    unsafe {
        (*d).lock.lock();
        let _ = sys::lseek((*d).fd, 0, sys::SEEK_SET);
        (*d).pos = 0;
        (*d).len = 0;
        (*d).tell = 0;
        (*d).lock.unlock();
    }
}

/// `telldir(3)`.
///
/// # Safety
/// `d` must be an open directory stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn telldir(d: *mut Dir) -> c_long {
    // SAFETY: caller contract.
    unsafe { (*d).tell }
}

/// `seekdir(3)`.
///
/// # Safety
/// `d` must be an open directory stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn seekdir(d: *mut Dir, off: c_long) {
    // SAFETY: caller contract.
    unsafe {
        (*d).lock.lock();
        let _ = sys::lseek((*d).fd, off, sys::SEEK_SET);
        (*d).pos = 0;
        (*d).len = 0;
        (*d).tell = off;
        (*d).lock.unlock();
    }
}

type Filter = Option<unsafe extern "C" fn(*const Dirent) -> c_int>;
type Compar = Option<unsafe extern "C" fn(*const *const Dirent, *const *const Dirent) -> c_int>;

/// `scandir(3)`.
///
/// # Safety
/// `path` must be NUL-terminated; `namelist` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn scandir(
    path: *const c_char,
    namelist: *mut *mut *mut Dirent,
    filter: Filter,
    compar: Compar,
) -> c_int {
    // SAFETY: forwarded.
    let d = unsafe { opendir(path) };
    if d.is_null() {
        return -1;
    }
    let mut list: *mut *mut Dirent = ptr::null_mut();
    let mut count = 0usize;
    let mut cap = 0usize;
    let fail = |list: *mut *mut Dirent, count: usize| {
        // SAFETY: entries and the array are our blocks.
        unsafe {
            for i in 0..count {
                malloc::dealloc(*list.add(i) as *mut u8);
            }
            malloc::dealloc(list as *mut u8);
        }
        -1
    };
    loop {
        Errno(0).set();
        // SAFETY: `d` is open.
        let e = unsafe { readdir(d) };
        if e.is_null() {
            if Errno::get() != Errno(0) {
                // SAFETY: `d` is open.
                unsafe { closedir(d) };
                return fail(list, count);
            }
            break;
        }
        // SAFETY: `e` is a valid entry.
        if let Some(f) = filter
            && unsafe { f(e) } == 0
        {
            continue;
        }
        if count == cap {
            cap = (cap * 2).max(32);
            // SAFETY: `list` is null or our block.
            let new = unsafe { malloc::realloc_impl(list as *mut u8, cap * 8) } as *mut *mut Dirent;
            if new.is_null() {
                // SAFETY: `d` is open.
                unsafe { closedir(d) };
                return fail(list, count);
            }
            list = new;
        }
        // SAFETY: `e` has `d_reclen` bytes.
        let len = unsafe { (*e).d_reclen as usize };
        let copy = malloc::alloc(len) as *mut Dirent;
        if copy.is_null() {
            // SAFETY: `d` is open.
            unsafe { closedir(d) };
            return fail(list, count);
        }
        // SAFETY: both blocks hold `len` bytes.
        unsafe {
            ptr::copy_nonoverlapping(e as *const u8, copy as *mut u8, len);
            *list.add(count) = copy;
        }
        count += 1;
    }
    // SAFETY: `d` is open.
    unsafe { closedir(d) };
    if let Some(c) = compar
        && count > 1
    {
        // SAFETY: the array holds `count` valid pointers.
        unsafe {
            crate::stdlib::sort::qsort(
                list as *mut c_void,
                count,
                8,
                core::mem::transmute::<
                    unsafe extern "C" fn(*const *const Dirent, *const *const Dirent) -> c_int,
                    unsafe extern "C" fn(*const c_void, *const c_void) -> c_int,
                >(c),
            );
        }
    }
    // SAFETY: caller contract.
    unsafe { *namelist = list };
    count as c_int
}

/// `alphasort(3)`.
///
/// # Safety
/// Both must point to valid entry pointers.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn alphasort(a: *const *const Dirent, b: *const *const Dirent) -> c_int {
    // SAFETY: caller contract.
    unsafe { crate::string::str::strcoll((**a).d_name.as_ptr(), (**b).d_name.as_ptr()) }
}
