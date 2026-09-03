//! `<stdio.h>`: buffered streams.
//!
//! A [`File`] wraps a file descriptor (or, for `fmemopen` /
//! `open_memstream`, an in-memory cookie) with one buffer used for either
//! reading or writing at a time. The layout is:
//!
//! ```text
//!  base                      base+UNGET                          base+UNGET+cap
//!  | UNGET pushback bytes  |  data area                                |
//!                             reading: valid bytes in [rpos, rend) (indices from base)
//!                             writing: pending bytes in [UNGET, UNGET+wpos)
//! ```
//!
//! Every stream has a recursive lock so that the C API is thread safe
//! and `flockfile` nests. Single-threaded processes skip the atomic
//! part of the lock.
//!
//! Formatting lives in [`printf`], scanning in [`scanf`].

pub mod printf;
pub mod scanf;

use printf::Sink as _;

use crate::c_char;
use crate::errno::Errno;
use crate::malloc;
use crate::sync::{Mutex, RawMutex};
use crate::sys::{
    self, O_ACCMODE, O_APPEND, O_CLOEXEC, O_CREAT, O_EXCL, O_RDONLY, O_RDWR, O_TRUNC, O_WRONLY,
    SEEK_CUR, SEEK_END, SEEK_SET,
};
use core::cell::{Cell, UnsafeCell};
use core::ffi::{c_int, c_long, c_void};
use core::ptr;
use core::sync::atomic::{AtomicU32, Ordering};

/// Default buffer size.
pub const BUFSIZ: usize = 8192;

/// A stream operation failed; the stream's error flag and `errno` carry
/// the details.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StreamError;
/// Bytes reserved in front of the data area for `ungetc`.
const UNGET: usize = 8;
/// `EOF`.
pub const EOF: c_int = -1;

const F_READ: u32 = 1 << 0;
const F_WRITE: u32 = 1 << 1;
const F_APPEND: u32 = 1 << 2;
const F_EOF: u32 = 1 << 3;
const F_ERR: u32 = 1 << 4;
const F_LINE: u32 = 1 << 5;
const F_NOBUF: u32 = 1 << 6;
/// Buffering mode not yet decided (stdout): line buffered if a tty.
const F_LBF_UNKNOWN: u32 = 1 << 7;
/// The buffer was allocated by us and must be freed.
const F_OWN_BUF: u32 = 1 << 8;
/// The `File` itself is a static object and must not be freed.
const F_STATIC: u32 = 1 << 9;

const MODE_IDLE: u8 = 0;
const MODE_READ: u8 = 1;
const MODE_WRITE: u8 = 2;

/// Backend operations of a stream.
pub struct Ops {
    /// Reads into the slice; `Ok(0)` is end of file.
    pub read: unsafe fn(&mut File, &mut [u8]) -> sys::Result<usize>,
    /// Writes (possibly part of) the slice.
    pub write: unsafe fn(&mut File, &[u8]) -> sys::Result<usize>,
    /// Repositions; returns the new offset.
    pub seek: unsafe fn(&mut File, i64, c_int) -> sys::Result<i64>,
    /// Releases the underlying resource.
    pub close: unsafe fn(&mut File) -> sys::Result<()>,
}

unsafe fn fd_read(f: &mut File, buf: &mut [u8]) -> sys::Result<usize> {
    // SAFETY: the slice is valid.
    unsafe { sys::read(f.fd, buf.as_mut_ptr(), buf.len()) }
}
unsafe fn fd_write(f: &mut File, buf: &[u8]) -> sys::Result<usize> {
    // SAFETY: the slice is valid.
    unsafe { sys::write(f.fd, buf.as_ptr(), buf.len()) }
}
unsafe fn fd_seek(f: &mut File, off: i64, whence: c_int) -> sys::Result<i64> {
    sys::lseek(f.fd, off, whence)
}
unsafe fn fd_close(f: &mut File) -> sys::Result<()> {
    sys::close(f.fd)
}

static FD_OPS: Ops = Ops {
    read: fd_read,
    write: fd_write,
    seek: fd_seek,
    close: fd_close,
};

/// A recursive lock for streams. See the module documentation.
pub struct FileLock {
    raw: RawMutex,
    owner: AtomicU32,
    count: Cell<u32>,
    real: Cell<bool>,
}

impl FileLock {
    const fn new() -> Self {
        FileLock {
            raw: RawMutex::new(),
            owner: AtomicU32::new(0),
            count: Cell::new(0),
            real: Cell::new(false),
        }
    }

    fn lock(&self) {
        let me = crate::thread::tid();
        if self.owner.load(Ordering::Relaxed) == me {
            self.count.set(self.count.get() + 1);
            return;
        }
        let real = crate::thread::is_threaded();
        if real {
            self.raw.lock();
            // A lock taken before the process became multi-threaded did
            // not take `raw`; wait for its owner to release it.
            while self.owner.load(Ordering::Acquire) != 0 {
                sys::sched_yield();
            }
        }
        self.owner.store(me, Ordering::Relaxed);
        self.count.set(1);
        self.real.set(real);
    }

    fn try_lock(&self) -> bool {
        let me = crate::thread::tid();
        if self.owner.load(Ordering::Relaxed) == me {
            self.count.set(self.count.get() + 1);
            return true;
        }
        let real = crate::thread::is_threaded();
        if real {
            if !self.raw.try_lock() {
                return false;
            }
            if self.owner.load(Ordering::Acquire) != 0 {
                // Taken without the raw mutex before the process became
                // multi-threaded.
                // SAFETY: we just took `raw`.
                unsafe { self.raw.unlock() };
                return false;
            }
        }
        self.owner.store(me, Ordering::Relaxed);
        self.count.set(1);
        self.real.set(real);
        true
    }

    /// Fixes up the lock in a forked child (see `postfork`): the
    /// forking thread's own holds survive with its new tid; a lock held by
    /// any other thread of the parent is simply released.
    fn after_fork(&self, old_tid: u32, new_tid: u32) {
        if self.owner.load(Ordering::Relaxed) == old_tid && self.count.get() > 1 {
            // One level was `prefork`'s; the rest are the caller's.
            self.count.set(self.count.get() - 1);
            self.owner.store(new_tid, Ordering::Relaxed);
            return;
        }
        self.count.set(0);
        self.real.set(false);
        self.owner.store(0, Ordering::Relaxed);
        self.raw.force_unlock();
    }

    fn unlock(&self) {
        let n = self.count.get() - 1;
        self.count.set(n);
        if n == 0 {
            let real = self.real.get();
            self.real.set(false);
            self.owner.store(0, Ordering::Release);
            if real {
                // SAFETY: we took `raw` in `lock`.
                unsafe { self.raw.unlock() };
            }
        }
    }
}

/// The C `FILE`.
#[repr(C)]
pub struct File {
    lock: FileLock,
    /// The file descriptor, or -1 for closed / cookie streams.
    pub fd: c_int,
    flags: u32,
    mode: u8,
    base: *mut u8,
    cap: usize,
    rpos: usize,
    rend: usize,
    wpos: usize,
    ops: &'static Ops,
    /// Backend private data (memory streams).
    pub cookie: *mut c_void,
    next: *mut File,
    prev: *mut File,
}

impl File {
    const fn new_static(fd: c_int, flags: u32, buf: *mut u8, cap: usize) -> File {
        File {
            lock: FileLock::new(),
            fd,
            flags: flags | F_STATIC,
            mode: MODE_IDLE,
            base: buf,
            cap,
            rpos: UNGET,
            rend: UNGET,
            wpos: 0,
            ops: &FD_OPS,
            cookie: ptr::null_mut(),
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
        }
    }

    /// Allocates a new stream object for `fd` with the given flags.
    fn alloc(fd: c_int, flags: u32, ops: &'static Ops, cookie: *mut c_void) -> *mut File {
        let f = malloc::alloc(core::mem::size_of::<File>()) as *mut File;
        if f.is_null() {
            return f;
        }
        // SAFETY: fresh block of the right size.
        unsafe {
            f.write(File {
                lock: FileLock::new(),
                fd,
                flags,
                mode: MODE_IDLE,
                base: ptr::null_mut(),
                cap: 0,
                rpos: UNGET,
                rend: UNGET,
                wpos: 0,
                ops,
                cookie,
                next: ptr::null_mut(),
                prev: ptr::null_mut(),
            });
            register(f);
        }
        f
    }

    /// Makes sure a buffer exists (allocating the default one lazily so
    /// that `setvbuf` can still replace it).
    fn ensure_buf(&mut self) -> bool {
        if !self.base.is_null() {
            return true;
        }
        let cap = if self.flags & F_NOBUF != 0 { 1 } else { BUFSIZ };
        let buf = malloc::alloc(cap + UNGET);
        if buf.is_null() {
            self.flags |= F_ERR;
            return false;
        }
        self.base = buf;
        self.cap = cap;
        self.flags |= F_OWN_BUF;
        self.rpos = UNGET;
        self.rend = UNGET;
        self.wpos = 0;
        true
    }

    #[inline]
    fn data(&mut self) -> *mut u8 {
        // SAFETY: `base` has `UNGET + cap` bytes.
        unsafe { self.base.add(UNGET) }
    }

    /// Writes out pending output. Sets the error flag on failure.
    fn flush_write(&mut self) -> Result<(), StreamError> {
        let mut done = 0;
        while done < self.wpos {
            // SAFETY: the pending bytes are inside the buffer.
            let chunk =
                unsafe { core::slice::from_raw_parts(self.data().add(done), self.wpos - done) };
            // SAFETY: the ops are valid for this stream.
            match unsafe { (self.ops.write)(self, chunk) } {
                Ok(n) => done += n,
                Err(Errno::EINTR) => {}
                Err(e) => {
                    // Keep whatever could not be written.
                    // SAFETY: shifting within the buffer.
                    unsafe { ptr::copy(self.data().add(done), self.data(), self.wpos - done) };
                    self.wpos -= done;
                    self.flags |= F_ERR;
                    e.set();
                    return Err(StreamError);
                }
            }
        }
        self.wpos = 0;
        Ok(())
    }

    /// Switches the stream to write mode.
    fn prepare_write(&mut self) -> Result<(), StreamError> {
        if self.mode == MODE_WRITE {
            return Ok(());
        }
        if self.flags & F_WRITE == 0 {
            self.flags |= F_ERR;
            Errno::EBADF.set();
            return Err(StreamError);
        }
        if self.mode == MODE_READ && self.rpos < self.rend {
            // Unread buffered input: move the file position back so the
            // write lands where the program thinks it is.
            let back = (self.rend - self.rpos) as i64;
            // SAFETY: the ops are valid for this stream.
            let _ = unsafe { (self.ops.seek)(self, -back, SEEK_CUR) };
        }
        self.rpos = UNGET;
        self.rend = UNGET;
        if !self.ensure_buf() {
            return Err(StreamError);
        }
        if self.flags & F_LBF_UNKNOWN != 0 {
            self.flags &= !F_LBF_UNKNOWN;
            if isatty_fd(self.fd) {
                self.flags |= F_LINE;
            }
        }
        self.mode = MODE_WRITE;
        Ok(())
    }

    /// Writes `data`, buffering as the stream's mode dictates.
    pub fn write_bytes(&mut self, data: &[u8]) -> Result<(), StreamError> {
        self.prepare_write()?;
        if self.flags & F_NOBUF != 0 {
            return self.write_direct(data);
        }
        if data.len() > self.cap - self.wpos {
            self.flush_write()?;
            if data.len() >= self.cap {
                return self.write_direct(data);
            }
        }
        // SAFETY: there is room for `data` in the buffer.
        unsafe { ptr::copy_nonoverlapping(data.as_ptr(), self.data().add(self.wpos), data.len()) };
        self.wpos += data.len();
        if self.flags & F_LINE != 0 && crate::string::search::memrchr(data, b'\n').is_some() {
            self.flush_write()?;
        }
        Ok(())
    }

    /// Writes `data` straight to the backend.
    fn write_direct(&mut self, mut data: &[u8]) -> Result<(), StreamError> {
        while !data.is_empty() {
            // SAFETY: the ops are valid for this stream.
            match unsafe { (self.ops.write)(self, data) } {
                Ok(n) => data = &data[n..],
                Err(Errno::EINTR) => {}
                Err(e) => {
                    self.flags |= F_ERR;
                    e.set();
                    return Err(StreamError);
                }
            }
        }
        Ok(())
    }

    /// Writes one byte.
    #[inline]
    pub fn putc(&mut self, b: u8) -> Result<(), StreamError> {
        if self.mode == MODE_WRITE && self.wpos < self.cap && self.flags & (F_NOBUF | F_LINE) == 0 {
            // SAFETY: room in the buffer.
            unsafe { *self.data().add(self.wpos) = b };
            self.wpos += 1;
            return Ok(());
        }
        self.write_bytes(&[b])
    }

    /// Switches the stream to read mode.
    fn prepare_read(&mut self) -> Result<(), StreamError> {
        if self.mode == MODE_READ {
            return Ok(());
        }
        if self.flags & F_READ == 0 {
            self.flags |= F_ERR;
            Errno::EBADF.set();
            return Err(StreamError);
        }
        if self.mode == MODE_WRITE {
            self.flush_write()?;
        }
        if !self.ensure_buf() {
            return Err(StreamError);
        }
        self.rpos = UNGET;
        self.rend = UNGET;
        self.mode = MODE_READ;
        Ok(())
    }

    /// Refills the read buffer. Returns `Ok(false)` at end of file.
    fn fill(&mut self) -> Result<bool, StreamError> {
        self.prepare_read()?;
        if self.flags & F_EOF != 0 {
            return Ok(false);
        }
        // Interactive convenience: flush line-buffered stdout before
        // blocking for input.
        if self.fd == 0 {
            flush_line_buffered_stdout();
        }
        self.rpos = UNGET;
        self.rend = UNGET;
        let cap = self.cap;
        loop {
            // SAFETY: the data area has `cap` bytes.
            let buf = unsafe { core::slice::from_raw_parts_mut(self.data(), cap) };
            // SAFETY: the ops are valid for this stream.
            match unsafe { (self.ops.read)(self, buf) } {
                Ok(0) => {
                    self.flags |= F_EOF;
                    return Ok(false);
                }
                Ok(n) => {
                    self.rend = UNGET + n;
                    return Ok(true);
                }
                Err(Errno::EINTR) => {}
                Err(e) => {
                    self.flags |= F_ERR;
                    e.set();
                    return Err(StreamError);
                }
            }
        }
    }

    /// Reads one byte.
    #[inline]
    pub fn getc(&mut self) -> Option<u8> {
        if self.mode == MODE_READ && self.rpos < self.rend {
            // SAFETY: inside the valid region.
            let b = unsafe { *self.base.add(self.rpos) };
            self.rpos += 1;
            return Some(b);
        }
        self.getc_slow()
    }

    fn getc_slow(&mut self) -> Option<u8> {
        match self.fill() {
            Ok(true) => {
                // SAFETY: `fill` made at least one byte available.
                let b = unsafe { *self.base.add(self.rpos) };
                self.rpos += 1;
                Some(b)
            }
            _ => None,
        }
    }

    /// Pushes one byte back. Fails if the pushback area is full.
    pub fn ungetc(&mut self, b: u8) -> bool {
        if self.mode != MODE_READ && self.prepare_read().is_err() {
            return false;
        }
        if self.rpos == 0 {
            return false;
        }
        self.rpos -= 1;
        // SAFETY: `rpos` is inside the buffer.
        unsafe { *self.base.add(self.rpos) = b };
        self.flags &= !F_EOF;
        true
    }

    /// Reads up to `out.len()` bytes; returns how many were read (fewer
    /// only at end of file or on error).
    pub fn read_bytes(&mut self, out: &mut [u8]) -> usize {
        if self.prepare_read().is_err() {
            return 0;
        }
        let mut done = 0;
        while done < out.len() {
            let avail = self.rend - self.rpos;
            if avail > 0 {
                let n = avail.min(out.len() - done);
                // SAFETY: both ranges are valid.
                unsafe {
                    ptr::copy_nonoverlapping(self.base.add(self.rpos), out[done..].as_mut_ptr(), n)
                };
                self.rpos += n;
                done += n;
                continue;
            }
            let want = out.len() - done;
            if want >= self.cap {
                // Large read: skip the buffer.
                if self.flags & F_EOF != 0 {
                    break;
                }
                // SAFETY: the ops are valid for this stream.
                match unsafe { (self.ops.read)(self, &mut out[done..]) } {
                    Ok(0) => {
                        self.flags |= F_EOF;
                        break;
                    }
                    Ok(n) => done += n,
                    Err(Errno::EINTR) => {}
                    Err(e) => {
                        self.flags |= F_ERR;
                        e.set();
                        break;
                    }
                }
                continue;
            }
            match self.fill() {
                Ok(true) => {}
                _ => break,
            }
        }
        done
    }

    /// Repositions the stream.
    pub fn seek(&mut self, offset: i64, whence: c_int) -> Result<i64, StreamError> {
        let mut offset = offset;
        if self.mode == MODE_WRITE {
            self.flush_write()?;
        } else if self.mode == MODE_READ && whence == SEEK_CUR {
            // Account for buffered but unread input.
            offset -= (self.rend - self.rpos) as i64;
        }
        self.rpos = UNGET;
        self.rend = UNGET;
        self.mode = MODE_IDLE;
        // SAFETY: the ops are valid for this stream.
        match unsafe { (self.ops.seek)(self, offset, whence) } {
            Ok(pos) => {
                self.flags &= !F_EOF;
                Ok(pos)
            }
            Err(e) => {
                e.set();
                Err(StreamError)
            }
        }
    }

    /// Current position.
    pub fn tell(&mut self) -> Result<i64, StreamError> {
        // SAFETY: the ops are valid for this stream.
        let pos = match unsafe { (self.ops.seek)(self, 0, SEEK_CUR) } {
            Ok(p) => p,
            Err(e) => {
                e.set();
                return Err(StreamError);
            }
        };
        Ok(match self.mode {
            MODE_READ => pos - (self.rend - self.rpos) as i64,
            MODE_WRITE => pos + self.wpos as i64,
            _ => pos,
        })
    }

    /// Flushes pending output (a no-op for input streams).
    pub fn flush(&mut self) -> Result<(), StreamError> {
        if self.mode == MODE_WRITE {
            self.flush_write()
        } else {
            Ok(())
        }
    }

    /// True if the stream is unbuffered.
    pub fn is_unbuffered(&self) -> bool {
        self.flags & F_NOBUF != 0
    }
}

// ---------------------------------------------------------------------
// Locking guard.

/// A locked stream. Unlocks on drop.
pub struct Locked<'a> {
    file: &'a mut File,
}

impl core::ops::Deref for Locked<'_> {
    type Target = File;
    fn deref(&self) -> &File {
        self.file
    }
}

impl core::ops::DerefMut for Locked<'_> {
    fn deref_mut(&mut self) -> &mut File {
        self.file
    }
}

impl Drop for Locked<'_> {
    fn drop(&mut self) {
        self.file.lock.unlock();
    }
}

/// Locks `f` for the duration of the returned guard.
///
/// # Safety
/// `f` must be a valid open stream.
pub unsafe fn lock<'a>(f: *mut File) -> Locked<'a> {
    // SAFETY: caller contract; the lock makes the `&mut` exclusive among
    // threads (recursion happens on the same thread, sequentially).
    unsafe {
        (*f).lock.lock();
        Locked { file: &mut *f }
    }
}

/// Like [`lock`] but gives up if another thread holds the stream.
///
/// # Safety
/// `f` must be a valid open stream.
pub unsafe fn try_lock<'a>(f: *mut File) -> Option<Locked<'a>> {
    // SAFETY: as for `lock`.
    unsafe {
        if (*f).lock.try_lock() {
            Some(Locked { file: &mut *f })
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------
// The standard streams and the open-file list.

struct StaticFile(UnsafeCell<File>);
// SAFETY: access goes through the per-file lock.
unsafe impl Sync for StaticFile {}

struct StaticBuf(UnsafeCell<[u8; BUFSIZ + UNGET]>);
// SAFETY: only accessed through the owning file, under its lock.
unsafe impl Sync for StaticBuf {}

static STDIN_BUF: StaticBuf = StaticBuf(UnsafeCell::new([0; BUFSIZ + UNGET]));
static STDOUT_BUF: StaticBuf = StaticBuf(UnsafeCell::new([0; BUFSIZ + UNGET]));
static STDERR_BUF: StaticBuf = StaticBuf(UnsafeCell::new([0; BUFSIZ + UNGET]));

static STDIN: StaticFile = StaticFile(UnsafeCell::new(File::new_static(
    0,
    F_READ,
    STDIN_BUF.0.get() as *mut u8,
    BUFSIZ,
)));
static STDOUT: StaticFile = StaticFile(UnsafeCell::new(File::new_static(
    1,
    F_WRITE | F_LBF_UNKNOWN,
    STDOUT_BUF.0.get() as *mut u8,
    BUFSIZ,
)));
static STDERR: StaticFile = StaticFile(UnsafeCell::new(File::new_static(
    2,
    F_WRITE | F_NOBUF,
    STDERR_BUF.0.get() as *mut u8,
    BUFSIZ,
)));

/// The C `stdin` variable.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut stdin: *mut File = STDIN.0.get();
/// The C `stdout` variable.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut stdout: *mut File = STDOUT.0.get();
/// The C `stderr` variable.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut stderr: *mut File = STDERR.0.get();

struct FileList(*mut File);
// SAFETY: guarded by the mutex.
unsafe impl Send for FileList {}
static FILES: Mutex<FileList> = Mutex::new(FileList(ptr::null_mut()));

/// Links the standard streams into the open-file list. Called at startup.
pub fn init() {
    // SAFETY: startup is single-threaded.
    unsafe {
        register(STDIN.0.get());
        register(STDOUT.0.get());
        register(STDERR.0.get());
    }
}

/// # Safety
/// `f` must be a valid stream not on the list.
unsafe fn register(f: *mut File) {
    let mut list = FILES.lock();
    // SAFETY: caller contract.
    unsafe {
        (*f).next = list.0;
        (*f).prev = ptr::null_mut();
        if !list.0.is_null() {
            (*list.0).prev = f;
        }
    }
    list.0 = f;
}

/// # Safety
/// `f` must be on the list.
unsafe fn unregister(f: *mut File) {
    let mut list = FILES.lock();
    // SAFETY: caller contract.
    unsafe {
        let (prev, next) = ((*f).prev, (*f).next);
        if prev.is_null() {
            list.0 = next;
        } else {
            (*prev).next = next;
        }
        if !next.is_null() {
            (*next).prev = prev;
        }
    }
}

/// Flushes every open output stream. Used by `exit` and `fflush(NULL)`.
///
/// The list lock is held for the whole walk so no stream can be closed
/// (and freed) underneath it: `fclose` unregisters a stream before
/// locking it, and registration never happens under a stream lock, so
/// the only way to wait here is a stream another thread holds while it
/// opens or closes a file, which glibc's `_IO_flush_all` accepts too.
/// At `exit`, streams held by other threads (typically one blocked in a
/// read) are skipped instead of waited for, since those threads never
/// get to release them.
pub fn flush_all(at_exit: bool) -> c_int {
    let mut result = 0;
    let list = FILES.lock();
    let mut f = list.0;
    while !f.is_null() {
        // SAFETY: streams on the list are valid while the list lock is
        // held.
        unsafe {
            let guard = if at_exit { try_lock(f) } else { Some(lock(f)) };
            if let Some(mut guard) = guard
                && guard.flush().is_err()
            {
                result = EOF;
            }
            f = (*f).next;
        }
    }
    drop(list);
    result
}

/// Locks every stream (and the stream list) before `fork`.
pub fn prefork() {
    FILES.raw().lock();
    let mut f = FILES.lock_unchecked_head();
    while !f.is_null() {
        // SAFETY: streams on the list are valid while the list lock is held.
        unsafe {
            (*f).lock.lock();
            f = (*f).next;
        }
    }
}

/// Undoes [`prefork`]. In the child the forking thread has a new tid, so
/// the locks are reset rather than unlocked.
///
/// # Safety
/// Must follow [`prefork`] on the same thread.
pub unsafe fn postfork(child: bool) {
    let old_tid = crate::thread::tid();
    let new_tid = if child { sys::gettid() as u32 } else { old_tid };
    let mut f = FILES.lock_unchecked_head();
    while !f.is_null() {
        // SAFETY: as in `prefork`.
        unsafe {
            if child {
                (*f).lock.after_fork(old_tid, new_tid);
            } else {
                (*f).lock.unlock();
            }
            f = (*f).next;
        }
    }
    if child {
        FILES.raw().force_unlock();
    } else {
        // SAFETY: taken in `prefork`.
        unsafe { FILES.raw().unlock() };
    }
}

impl Mutex<FileList> {
    /// The list head, for callers that already hold the raw lock.
    fn lock_unchecked_head(&self) -> *mut File {
        // SAFETY: callers hold the raw lock.
        unsafe { (*self.value_ptr()).0 }
    }
}

fn flush_line_buffered_stdout() {
    let out = STDOUT.0.get();
    // SAFETY: `out` is the static stdout; try_lock avoids deadlocking
    // against a thread that holds it while reading stdin.
    unsafe {
        if (*out).lock.try_lock() {
            if (*out).flags & F_LINE != 0 {
                let _ = (*out).flush();
            }
            (*out).lock.unlock();
        }
    }
}

/// `isatty` on a descriptor.
fn isatty_fd(fd: c_int) -> bool {
    let mut termios = [0u8; 64];
    // SAFETY: TCGETS writes a `struct termios` (60 bytes) into the buffer.
    unsafe { sys::ioctl(fd, sys::TCGETS, termios.as_mut_ptr() as usize).is_ok() }
}

// ---------------------------------------------------------------------
// Opening and closing.

/// Parses an `fopen` mode string into stream flags and `open` flags.
fn parse_mode(mode: &[u8]) -> Option<(u32, c_int)> {
    let (mut flags, mut oflags) = match mode.first()? {
        b'r' => (F_READ, O_RDONLY),
        b'w' => (F_WRITE, O_WRONLY | O_CREAT | O_TRUNC),
        b'a' => (F_WRITE | F_APPEND, O_WRONLY | O_CREAT | O_APPEND),
        _ => return None,
    };
    for &c in &mode[1..] {
        match c {
            b'+' => {
                flags |= F_READ | F_WRITE;
                oflags = (oflags & !O_ACCMODE) | O_RDWR;
            }
            b'b' => {}
            b'x' => oflags |= O_EXCL,
            b'e' => oflags |= O_CLOEXEC,
            _ => {}
        }
    }
    Some((flags, oflags))
}

/// `fopen(3)`.
///
/// # Safety
/// `path` and `mode` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fopen(path: *const c_char, mode: *const c_char) -> *mut File {
    // SAFETY: forwarded.
    let mode_bytes =
        unsafe { core::slice::from_raw_parts(mode as *const u8, crate::string::str::strlen(mode)) };
    let Some((flags, oflags)) = parse_mode(mode_bytes) else {
        Errno::EINVAL.set();
        return ptr::null_mut();
    };
    // SAFETY: forwarded.
    let fd = match unsafe {
        sys::openat(
            sys::AT_FDCWD,
            path as *const u8,
            oflags | crate::sys::O_LARGEFILE,
            0o666,
        )
    } {
        Ok(fd) => fd,
        Err(e) => {
            e.set();
            return ptr::null_mut();
        }
    };
    let f = File::alloc(fd, flags, &FD_OPS, ptr::null_mut());
    if f.is_null() {
        let _ = sys::close(fd);
        Errno::ENOMEM.set();
    }
    f
}

/// `fdopen(3)`.
///
/// # Safety
/// `mode` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fdopen(fd: c_int, mode: *const c_char) -> *mut File {
    // SAFETY: forwarded.
    let mode_bytes =
        unsafe { core::slice::from_raw_parts(mode as *const u8, crate::string::str::strlen(mode)) };
    let Some((flags, oflags)) = parse_mode(mode_bytes) else {
        Errno::EINVAL.set();
        return ptr::null_mut();
    };
    // SAFETY: F_GETFL takes no argument.
    let Ok(cur) = (unsafe { sys::fcntl(fd, sys::F_GETFL, 0) }) else {
        Errno::EBADF.set();
        return ptr::null_mut();
    };
    if flags & F_APPEND != 0 && cur & O_APPEND == 0 {
        // SAFETY: F_SETFL takes an int.
        let _ = unsafe { sys::fcntl(fd, sys::F_SETFL, (cur | O_APPEND) as usize) };
    }
    if oflags & sys::O_CLOEXEC != 0 {
        // SAFETY: F_SETFD takes an int.
        let _ = unsafe { sys::fcntl(fd, sys::F_SETFD, sys::FD_CLOEXEC as usize) };
    }
    let f = File::alloc(fd, flags, &FD_OPS, ptr::null_mut());
    if f.is_null() {
        Errno::ENOMEM.set();
    }
    f
}

/// `freopen(3)`. With a NULL path the stream's own file is reopened with
/// the new mode (through `/proc/self/fd`), keeping its descriptor number.
///
/// # Safety
/// `path` and `mode` must be NUL-terminated; `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn freopen(
    path: *const c_char,
    mode: *const c_char,
    f: *mut File,
) -> *mut File {
    // SAFETY: forwarded.
    let mode_bytes =
        unsafe { core::slice::from_raw_parts(mode as *const u8, crate::string::str::strlen(mode)) };
    let Some((flags, oflags)) = parse_mode(mode_bytes) else {
        Errno::EINVAL.set();
        return ptr::null_mut();
    };
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    let _ = g.flush();
    if path.is_null() {
        // Reopen the same file: open it again by descriptor path, then
        // move the new descriptor onto the old number.
        if g.fd < 0 {
            Errno::EBADF.set();
            return ptr::null_mut();
        }
        let mut p = [0u8; 32];
        let mut w = crate::fmt::SliceWriter::new(&mut p);
        let _ = core::fmt::write(&mut w, format_args!("/proc/self/fd/{}", g.fd));
        // SAFETY: NUL-terminated path in a local buffer.
        let newfd = match unsafe {
            sys::openat(
                sys::AT_FDCWD,
                p.as_ptr(),
                oflags | crate::sys::O_LARGEFILE,
                0o666,
            )
        } {
            Ok(fd) => fd,
            Err(e) => {
                e.set();
                return ptr::null_mut();
            }
        };
        if newfd != g.fd {
            // SAFETY: both descriptors are ours.
            let r = unsafe {
                crate::arch::syscall3(crate::arch::nr::DUP3, newfd as usize, g.fd as usize, 0)
            };
            let _ = sys::close(newfd);
            if let Err(e) = sys::check(r) {
                e.set();
                return ptr::null_mut();
            }
        }
    } else {
        // Open first, then move the new descriptor onto the stream's old
        // number so `fileno` (and anything inherited by children) stays
        // the same. Memory streams have no descriptor; their cookie is
        // released.
        // SAFETY: forwarded.
        let newfd = match unsafe {
            sys::openat(
                sys::AT_FDCWD,
                path as *const u8,
                oflags | crate::sys::O_LARGEFILE,
                0o666,
            )
        } {
            Ok(fd) => fd,
            Err(e) => {
                if g.fd >= 0 {
                    // SAFETY: the ops are valid for this stream.
                    let _ = unsafe { (g.ops.close)(&mut g) };
                }
                g.fd = -1;
                e.set();
                return ptr::null_mut();
            }
        };
        if g.fd >= 0 && newfd != g.fd {
            // SAFETY: both descriptors are ours.
            let r = unsafe {
                crate::arch::syscall3(crate::arch::nr::DUP3, newfd as usize, g.fd as usize, 0)
            };
            let _ = sys::close(newfd);
            if let Err(e) = sys::check(r) {
                let _ = sys::close(g.fd);
                g.fd = -1;
                e.set();
                return ptr::null_mut();
            }
        } else {
            if g.fd < 0 {
                // SAFETY: the ops are valid for this stream.
                let _ = unsafe { (g.ops.close)(&mut g) };
            }
            g.fd = newfd;
        }
    }
    g.flags = (g.flags & (F_STATIC | F_OWN_BUF)) | flags;
    g.mode = MODE_IDLE;
    g.rpos = UNGET;
    g.rend = UNGET;
    g.wpos = 0;
    g.ops = &FD_OPS;
    f
}

/// `fclose(3)`.
///
/// # Safety
/// `f` must be a valid open stream, not used afterwards.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fclose(f: *mut File) -> c_int {
    // Leave the list first so `flush_all`, which walks it under the list
    // lock, can never reach a stream that is being freed.
    // SAFETY: forwarded.
    unsafe { unregister(f) };
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    let mut result = if g.flush().is_err() { EOF } else { 0 };
    // SAFETY: the ops are valid for this stream.
    if unsafe { (g.ops.close)(&mut g) }.is_err() {
        result = EOF;
    }
    g.fd = -1;
    let flags = g.flags;
    let base = g.base;
    drop(g);
    // SAFETY: nobody else may use the stream now.
    unsafe {
        if flags & F_OWN_BUF != 0 {
            malloc::dealloc(base);
        }
        if flags & F_STATIC == 0 {
            malloc::dealloc(f as *mut u8);
        } else {
            (*f).base = ptr::null_mut();
            (*f).flags &= !F_OWN_BUF;
        }
    }
    result
}

/// `fflush(3)`; a NULL stream flushes every stream.
///
/// # Safety
/// `f` must be NULL or a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fflush(f: *mut File) -> c_int {
    if f.is_null() {
        return flush_all(false);
    }
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    if g.flush().is_err() { EOF } else { 0 }
}

/// `setvbuf(3)`.
///
/// # Safety
/// `f` must be a valid stream; `buf` NULL or valid for `size` bytes for
/// the life of the stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn setvbuf(
    f: *mut File,
    buf: *mut c_char,
    mode: c_int,
    size: usize,
) -> c_int {
    const IOFBF: c_int = 0;
    const IOLBF: c_int = 1;
    const IONBF: c_int = 2;
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    g.flags &= !(F_LINE | F_NOBUF | F_LBF_UNKNOWN);
    match mode {
        IOFBF => {}
        IOLBF => g.flags |= F_LINE,
        IONBF => {
            g.flags |= F_NOBUF;
            // Reads must not pull ahead into the buffer either.
            if !g.base.is_null() {
                g.cap = 1;
            }
        }
        _ => {
            Errno::EINVAL.set();
            return -1;
        }
    }
    if !buf.is_null() && size > UNGET {
        if g.flags & F_OWN_BUF != 0 {
            // SAFETY: we allocated it.
            unsafe { malloc::dealloc(g.base) };
            g.flags &= !F_OWN_BUF;
        }
        g.base = buf as *mut u8;
        g.cap = size - UNGET;
        g.rpos = UNGET;
        g.rend = UNGET;
        g.wpos = 0;
    }
    0
}

/// `setbuf(3)`.
///
/// # Safety
/// As for [`setvbuf`] with `BUFSIZ` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn setbuf(f: *mut File, buf: *mut c_char) {
    // SAFETY: forwarded.
    unsafe { setvbuf(f, buf, if buf.is_null() { 2 } else { 0 }, BUFSIZ) };
}

/// `setbuffer(3)`.
///
/// # Safety
/// As for [`setvbuf`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn setbuffer(f: *mut File, buf: *mut c_char, size: usize) {
    // SAFETY: forwarded.
    unsafe { setvbuf(f, buf, if buf.is_null() { 2 } else { 0 }, size) };
}

/// `setlinebuf(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn setlinebuf(f: *mut File) {
    // SAFETY: forwarded.
    unsafe { setvbuf(f, ptr::null_mut(), 1, 0) };
}

// ---------------------------------------------------------------------
// Character and string I/O.

/// `fputc(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fputc(c: c_int, f: *mut File) -> c_int {
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    if g.putc(c as u8).is_ok() {
        c as u8 as c_int
    } else {
        EOF
    }
}

/// `putc(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn putc(c: c_int, f: *mut File) -> c_int {
    // SAFETY: forwarded.
    unsafe { fputc(c, f) }
}

/// `putc_unlocked(3)`: the lock is recursive, so this simply locks too.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn putc_unlocked(c: c_int, f: *mut File) -> c_int {
    // SAFETY: forwarded.
    unsafe { fputc(c, f) }
}

/// `putchar(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn putchar(c: c_int) -> c_int {
    // SAFETY: stdout is always valid.
    unsafe { fputc(c, stdout) }
}

/// `putchar_unlocked(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn putchar_unlocked(c: c_int) -> c_int {
    putchar(c)
}

/// `fputs(3)`.
///
/// # Safety
/// `s` must be NUL-terminated; `f` a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fputs(s: *const c_char, f: *mut File) -> c_int {
    // SAFETY: forwarded.
    let bytes =
        unsafe { core::slice::from_raw_parts(s as *const u8, crate::string::str::strlen(s)) };
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    if g.write_bytes(bytes).is_ok() { 1 } else { EOF }
}

/// `puts(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn puts(s: *const c_char) -> c_int {
    // SAFETY: forwarded.
    let bytes =
        unsafe { core::slice::from_raw_parts(s as *const u8, crate::string::str::strlen(s)) };
    // SAFETY: stdout is always valid.
    let mut g = unsafe { lock(stdout) };
    if g.write_bytes(bytes).is_ok() && g.putc(b'\n').is_ok() {
        1
    } else {
        EOF
    }
}

/// `fwrite(3)`.
///
/// # Safety
/// `p` must be valid for `size * n` bytes; `f` a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fwrite(p: *const c_void, size: usize, n: usize, f: *mut File) -> usize {
    let Some(total) = size.checked_mul(n) else {
        Errno::EOVERFLOW.set();
        return 0;
    };
    if total == 0 {
        return 0;
    }
    // SAFETY: forwarded.
    let data = unsafe { core::slice::from_raw_parts(p as *const u8, total) };
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    if g.write_bytes(data).is_ok() { n } else { 0 }
}

/// `fgetc(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fgetc(f: *mut File) -> c_int {
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    match g.getc() {
        Some(b) => b as c_int,
        None => EOF,
    }
}

/// `getc(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getc(f: *mut File) -> c_int {
    // SAFETY: forwarded.
    unsafe { fgetc(f) }
}

/// `getc_unlocked(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getc_unlocked(f: *mut File) -> c_int {
    // SAFETY: forwarded.
    unsafe { fgetc(f) }
}

/// `getchar(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getchar() -> c_int {
    // SAFETY: stdin is always valid.
    unsafe { fgetc(stdin) }
}

/// `getchar_unlocked(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getchar_unlocked() -> c_int {
    getchar()
}

/// `ungetc(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ungetc(c: c_int, f: *mut File) -> c_int {
    if c == EOF {
        return EOF;
    }
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    if g.ungetc(c as u8) {
        c as u8 as c_int
    } else {
        EOF
    }
}

/// `fgets(3)`.
///
/// # Safety
/// `s` must be valid for `n` bytes; `f` a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fgets(s: *mut c_char, n: c_int, f: *mut File) -> *mut c_char {
    if n <= 0 {
        Errno::EINVAL.set();
        return ptr::null_mut();
    }
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    let want = (n - 1) as usize;
    let mut got = 0;
    while got < want {
        if g.mode != MODE_READ || g.rpos >= g.rend {
            match g.fill() {
                Ok(true) => {}
                Ok(false) => break,
                Err(StreamError) => return ptr::null_mut(),
            }
        }
        // Copy up to the newline or the end of the buffered data.
        // SAFETY: `[rpos, rend)` is valid buffered input.
        let avail = unsafe { core::slice::from_raw_parts(g.base.add(g.rpos), g.rend - g.rpos) };
        let take = avail.len().min(want - got);
        let (copy, done) = match crate::string::search::memchr(&avail[..take], b'\n') {
            Some(i) => (i + 1, true),
            None => (take, false),
        };
        // SAFETY: `s` has room for `want` bytes.
        unsafe { ptr::copy_nonoverlapping(avail.as_ptr(), (s as *mut u8).add(got), copy) };
        got += copy;
        g.rpos += copy;
        if done {
            break;
        }
    }
    if got == 0 && want > 0 {
        return ptr::null_mut();
    }
    // SAFETY: `got < n`.
    unsafe { *s.add(got) = 0 };
    s
}

/// `fread(3)`.
///
/// # Safety
/// `p` must be valid for `size * n` bytes; `f` a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fread(p: *mut c_void, size: usize, n: usize, f: *mut File) -> usize {
    let Some(total) = size.checked_mul(n) else {
        Errno::EOVERFLOW.set();
        return 0;
    };
    if total == 0 {
        return 0;
    }
    // SAFETY: forwarded.
    let out = unsafe { core::slice::from_raw_parts_mut(p as *mut u8, total) };
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    g.read_bytes(out) / size
}

/// `getdelim(3)`.
///
/// # Safety
/// `lineptr` and `n` must be valid; `*lineptr` NULL or a `malloc` block
/// of `*n` bytes; `f` a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getdelim(
    lineptr: *mut *mut c_char,
    n: *mut usize,
    delim: c_int,
    f: *mut File,
) -> isize {
    if lineptr.is_null() || n.is_null() {
        Errno::EINVAL.set();
        return -1;
    }
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    // SAFETY: caller contract.
    let (mut buf, mut cap) = unsafe { (*lineptr as *mut u8, *n) };
    if buf.is_null() {
        cap = 0;
    }
    let mut len = 0usize;
    loop {
        if len + 2 > cap {
            let new_cap = (cap * 2).max(128);
            // SAFETY: `buf` is null or a malloc block.
            let new = unsafe { malloc::realloc_impl(buf, new_cap) };
            if new.is_null() {
                Errno::ENOMEM.set();
                // SAFETY: caller contract.
                unsafe {
                    *lineptr = buf as *mut c_char;
                    *n = cap;
                }
                return -1;
            }
            buf = new;
            cap = new_cap;
        }
        match g.getc() {
            Some(b) => {
                // SAFETY: `len + 1 < cap`.
                unsafe { *buf.add(len) = b };
                len += 1;
                if b == delim as u8 {
                    break;
                }
            }
            None => break,
        }
    }
    // SAFETY: `len < cap`; caller contract for the out-pointers.
    unsafe {
        *buf.add(len) = 0;
        *lineptr = buf as *mut c_char;
        *n = cap;
    }
    if len == 0 { -1 } else { len as isize }
}

/// `getline(3)`.
///
/// # Safety
/// As for [`getdelim`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getline(lineptr: *mut *mut c_char, n: *mut usize, f: *mut File) -> isize {
    // SAFETY: forwarded.
    unsafe { getdelim(lineptr, n, b'\n' as c_int, f) }
}

// ---------------------------------------------------------------------
// Positioning and status.

/// `fseeko(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fseeko(f: *mut File, offset: i64, whence: c_int) -> c_int {
    if !matches!(whence, SEEK_SET | SEEK_CUR | SEEK_END) {
        Errno::EINVAL.set();
        return -1;
    }
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    if g.seek(offset, whence).is_ok() {
        0
    } else {
        -1
    }
}

/// `fseek(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fseek(f: *mut File, offset: c_long, whence: c_int) -> c_int {
    // SAFETY: forwarded.
    unsafe { fseeko(f, offset, whence) }
}

/// `ftello(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ftello(f: *mut File) -> i64 {
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    g.tell().unwrap_or(-1)
}

/// `ftell(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ftell(f: *mut File) -> c_long {
    // SAFETY: forwarded.
    unsafe { ftello(f) }
}

/// `rewind(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn rewind(f: *mut File) {
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    let _ = g.seek(0, SEEK_SET);
    g.flags &= !F_ERR;
}

/// `fgetpos(3)`; `fpos_t` is a plain 64-bit offset.
///
/// # Safety
/// `f` must be a valid stream; `pos` a valid pointer.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fgetpos(f: *mut File, pos: *mut i64) -> c_int {
    // SAFETY: forwarded.
    let p = unsafe { ftello(f) };
    if p < 0 {
        return -1;
    }
    // SAFETY: caller contract.
    unsafe { *pos = p };
    0
}

/// `fsetpos(3)`.
///
/// # Safety
/// `f` must be a valid stream; `pos` a valid pointer.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fsetpos(f: *mut File, pos: *const i64) -> c_int {
    // SAFETY: forwarded.
    unsafe { fseeko(f, *pos, SEEK_SET) }
}

/// `feof(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn feof(f: *mut File) -> c_int {
    // SAFETY: forwarded.
    let g = unsafe { lock(f) };
    (g.flags & F_EOF != 0) as c_int
}

/// `ferror(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ferror(f: *mut File) -> c_int {
    // SAFETY: forwarded.
    let g = unsafe { lock(f) };
    (g.flags & F_ERR != 0) as c_int
}

/// `clearerr(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn clearerr(f: *mut File) {
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    g.flags &= !(F_EOF | F_ERR);
}

/// `fileno(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fileno(f: *mut File) -> c_int {
    // SAFETY: forwarded.
    let g = unsafe { lock(f) };
    if g.fd < 0 {
        Errno::EBADF.set();
        return -1;
    }
    g.fd
}

/// `flockfile(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn flockfile(f: *mut File) {
    // SAFETY: forwarded.
    unsafe { (*f).lock.lock() }
}

/// `ftrylockfile(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ftrylockfile(f: *mut File) -> c_int {
    // SAFETY: forwarded.
    if unsafe { (*f).lock.try_lock() } {
        0
    } else {
        1
    }
}

/// `funlockfile(3)`.
///
/// # Safety
/// `f` must be a valid stream locked by the caller.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn funlockfile(f: *mut File) {
    // SAFETY: forwarded.
    unsafe { (*f).lock.unlock() }
}

/// `perror(3)`.
///
/// # Safety
/// `s` must be NULL or NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn perror(s: *const c_char) {
    let err = Errno::get().0;
    // SAFETY: stderr is always valid.
    let mut g = unsafe { lock(stderr) };
    let mut out = printf::Staged::new(&mut g);
    if !s.is_null() {
        // SAFETY: forwarded.
        let prefix =
            unsafe { core::slice::from_raw_parts(s as *const u8, crate::string::str::strlen(s)) };
        if !prefix.is_empty() {
            let _ = out.write(prefix);
            let _ = out.write(b": ");
        }
    }
    let msg = crate::string::str::strerror(err);
    // SAFETY: strerror returns NUL-terminated strings.
    let msg =
        unsafe { core::slice::from_raw_parts(msg as *const u8, crate::string::str::strlen(msg)) };
    let _ = out.write(msg);
    let _ = out.write(b"\n");
    let _ = out.finish();
}

/// `remove(3)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn remove(path: *const c_char) -> c_int {
    // SAFETY: forwarded.
    let r = unsafe { sys::unlinkat(sys::AT_FDCWD, path as *const u8, 0) };
    let r = match r {
        // SAFETY: forwarded.
        Err(Errno::EISDIR) => unsafe {
            sys::unlinkat(sys::AT_FDCWD, path as *const u8, sys::AT_REMOVEDIR)
        },
        r => r,
    };
    crate::errno::CReturn::c_ret(r)
}

/// `rename(2)`.
///
/// # Safety
/// Both paths must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn rename(old: *const c_char, new: *const c_char) -> c_int {
    // SAFETY: forwarded.
    crate::errno::CReturn::c_ret(unsafe {
        sys::renameat(
            sys::AT_FDCWD,
            old as *const u8,
            sys::AT_FDCWD,
            new as *const u8,
        )
    })
}

/// `tmpfile(3)`: an anonymous temporary file in `/tmp`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tmpfile() -> *mut File {
    // SAFETY: literal NUL-terminated path.
    let fd = unsafe {
        sys::openat(
            sys::AT_FDCWD,
            c"/tmp".as_ptr() as *const u8,
            O_RDWR | crate::sys::O_TMPFILE | O_EXCL | O_CLOEXEC,
            0o600,
        )
    };
    let fd = match fd {
        Ok(fd) => fd,
        Err(_) => {
            // Fallback for file systems without O_TMPFILE: create and
            // unlink a randomly named file.
            let mut name = *b"/tmp/tmpf.XXXXXXXXXXXX\0";
            match randomize(&mut name[10..22]) {
                Ok(()) => {}
                Err(e) => {
                    e.set();
                    return ptr::null_mut();
                }
            }
            // SAFETY: NUL-terminated.
            let fd = match unsafe {
                sys::openat(
                    sys::AT_FDCWD,
                    name.as_ptr(),
                    O_RDWR | O_CREAT | O_EXCL | O_CLOEXEC,
                    0o600,
                )
            } {
                Ok(fd) => fd,
                Err(e) => {
                    e.set();
                    return ptr::null_mut();
                }
            };
            // SAFETY: NUL-terminated.
            let _ = unsafe { sys::unlinkat(sys::AT_FDCWD, name.as_ptr(), 0) };
            fd
        }
    };
    let f = File::alloc(fd, F_READ | F_WRITE, &FD_OPS, ptr::null_mut());
    if f.is_null() {
        let _ = sys::close(fd);
        Errno::ENOMEM.set();
    }
    f
}

/// Fills `out` with random characters from `[A-Za-z0-9]`.
pub fn randomize(out: &mut [u8]) -> sys::Result<()> {
    const ALPHABET: &[u8; 62] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    sys::getrandom_exact(out)?;
    for b in out.iter_mut() {
        *b = ALPHABET[(*b % 62) as usize];
    }
    Ok(())
}

// ---------------------------------------------------------------------
// Memory streams.

/// Cookie of `fmemopen` and `open_memstream` streams.
#[repr(C)]
struct MemCookie {
    buf: *mut u8,
    /// Capacity of `buf`.
    size: usize,
    /// Current logical length of the content.
    len: usize,
    pos: usize,
    /// `open_memstream`: where to publish the buffer and length.
    ptr_out: *mut *mut c_char,
    size_out: *mut usize,
    /// Buffer is ours to grow (`open_memstream`, or `fmemopen(NULL)`).
    growable: bool,
    owned: bool,
}

unsafe fn mem_read(f: &mut File, out: &mut [u8]) -> sys::Result<usize> {
    // SAFETY: the cookie is a live MemCookie.
    let c = unsafe { &mut *(f.cookie as *mut MemCookie) };
    let n = out.len().min(c.len.saturating_sub(c.pos));
    // SAFETY: `[pos, pos+n)` is inside the buffer.
    unsafe { ptr::copy_nonoverlapping(c.buf.add(c.pos), out.as_mut_ptr(), n) };
    c.pos += n;
    Ok(n)
}

unsafe fn mem_write(f: &mut File, data: &[u8]) -> sys::Result<usize> {
    // SAFETY: the cookie is a live MemCookie.
    let c = unsafe { &mut *(f.cookie as *mut MemCookie) };
    if f.flags & F_APPEND != 0 {
        c.pos = c.len;
    }
    let end = c.pos.checked_add(data.len()).ok_or(Errno::EOVERFLOW)?;
    if end + 1 > c.size {
        if !c.growable {
            if c.pos >= c.size {
                return Err(Errno::ENOSPC);
            }
            let n = c.size - c.pos;
            // SAFETY: fits in the buffer.
            unsafe { ptr::copy_nonoverlapping(data.as_ptr(), c.buf.add(c.pos), n) };
            c.pos += n;
            c.len = c.len.max(c.pos);
            return Ok(n);
        }
        let new_size = (end + 1).max(c.size * 2).max(64);
        // SAFETY: `buf` is our malloc block.
        let new = unsafe { malloc::realloc_impl(c.buf, new_size) };
        if new.is_null() {
            return Err(Errno::ENOMEM);
        }
        c.buf = new;
        c.size = new_size;
    }
    // SAFETY: fits in the buffer.
    unsafe {
        if c.pos > c.len {
            // A seek past the end: the gap reads as zeros, never as
            // whatever the block held before.
            ptr::write_bytes(c.buf.add(c.len), 0, c.pos - c.len);
        }
        ptr::copy_nonoverlapping(data.as_ptr(), c.buf.add(c.pos), data.len());
    }
    c.pos = end;
    if c.pos > c.len {
        c.len = c.pos;
    }
    if c.len < c.size {
        // SAFETY: inside the buffer.
        unsafe { *c.buf.add(c.len) = 0 };
    }
    mem_publish(c);
    Ok(data.len())
}

fn mem_publish(c: &mut MemCookie) {
    if !c.ptr_out.is_null() {
        // SAFETY: the out pointers were given to open_memstream.
        unsafe {
            *c.ptr_out = c.buf as *mut c_char;
            *c.size_out = c.len;
        }
    }
}

unsafe fn mem_seek(f: &mut File, off: i64, whence: c_int) -> sys::Result<i64> {
    // SAFETY: the cookie is a live MemCookie.
    let c = unsafe { &mut *(f.cookie as *mut MemCookie) };
    let base = match whence {
        SEEK_SET => 0,
        SEEK_CUR => c.pos as i64,
        SEEK_END => c.len as i64,
        _ => return Err(Errno::EINVAL),
    };
    let new = base.checked_add(off).ok_or(Errno::EOVERFLOW)?;
    if new < 0 || (!c.growable && new as usize > c.size) {
        return Err(Errno::EINVAL);
    }
    c.pos = new as usize;
    Ok(new)
}

unsafe fn mem_close(f: &mut File) -> sys::Result<()> {
    // SAFETY: the cookie is a live MemCookie; it is not used afterwards.
    unsafe {
        let c = &mut *(f.cookie as *mut MemCookie);
        mem_publish(c);
        if c.owned && c.ptr_out.is_null() {
            malloc::dealloc(c.buf);
        }
        malloc::dealloc(f.cookie as *mut u8);
    }
    Ok(())
}

static MEM_OPS: Ops = Ops {
    read: mem_read,
    write: mem_write,
    seek: mem_seek,
    close: mem_close,
};

/// `fmemopen(3)`.
///
/// # Safety
/// `buf` must be NULL or valid for `size` bytes for the stream's life;
/// `mode` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fmemopen(buf: *mut c_void, size: usize, mode: *const c_char) -> *mut File {
    // SAFETY: forwarded.
    let mode_bytes =
        unsafe { core::slice::from_raw_parts(mode as *const u8, crate::string::str::strlen(mode)) };
    let Some((flags, _)) = parse_mode(mode_bytes) else {
        Errno::EINVAL.set();
        return ptr::null_mut();
    };
    if size == 0 {
        Errno::EINVAL.set();
        return ptr::null_mut();
    }
    let mut owned = false;
    let buf = if buf.is_null() {
        owned = true;
        let p = malloc::alloc(size);
        if p.is_null() {
            Errno::ENOMEM.set();
            return ptr::null_mut();
        }
        // SAFETY: fresh block.
        unsafe { ptr::write_bytes(p, 0, size) };
        p
    } else {
        buf as *mut u8
    };
    // SAFETY: `buf` has `size` bytes.
    let len = unsafe {
        match mode_bytes[0] {
            b'r' => size,
            b'w' => 0,
            _ => crate::string::search::strnlen(buf, size),
        }
    };
    if mode_bytes[0] == b'w' && size > 0 {
        // SAFETY: inside the buffer.
        unsafe { *buf = 0 };
    }
    let cookie = malloc::alloc(core::mem::size_of::<MemCookie>()) as *mut MemCookie;
    if cookie.is_null() {
        if owned {
            // SAFETY: we allocated it.
            unsafe { malloc::dealloc(buf) };
        }
        Errno::ENOMEM.set();
        return ptr::null_mut();
    }
    // SAFETY: fresh block.
    unsafe {
        cookie.write(MemCookie {
            buf,
            size,
            len,
            pos: if mode_bytes[0] == b'a' { len } else { 0 },
            ptr_out: ptr::null_mut(),
            size_out: ptr::null_mut(),
            growable: false,
            owned,
        });
    }
    let f = File::alloc(-1, flags, &MEM_OPS, cookie as *mut c_void);
    if f.is_null() {
        // SAFETY: we allocated them.
        unsafe {
            if owned {
                malloc::dealloc(buf);
            }
            malloc::dealloc(cookie as *mut u8);
        }
        Errno::ENOMEM.set();
    }
    f
}

/// `open_memstream(3)`.
///
/// # Safety
/// `ptr_out` and `size_out` must stay valid for the stream's life.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn open_memstream(
    ptr_out: *mut *mut c_char,
    size_out: *mut usize,
) -> *mut File {
    let buf = malloc::alloc(64);
    let cookie = malloc::alloc(core::mem::size_of::<MemCookie>()) as *mut MemCookie;
    if buf.is_null() || cookie.is_null() {
        // SAFETY: null-safe frees of our own blocks.
        unsafe {
            malloc::dealloc(buf);
            malloc::dealloc(cookie as *mut u8);
        }
        Errno::ENOMEM.set();
        return ptr::null_mut();
    }
    // SAFETY: fresh blocks.
    unsafe {
        ptr::write_bytes(buf, 0, 64);
        cookie.write(MemCookie {
            buf,
            size: 64,
            len: 0,
            pos: 0,
            ptr_out,
            size_out,
            growable: true,
            owned: true,
        });
        mem_publish(&mut *cookie);
    }
    let f = File::alloc(-1, F_WRITE, &MEM_OPS, cookie as *mut c_void);
    if f.is_null() {
        // SAFETY: we allocated them.
        unsafe {
            malloc::dealloc(buf);
            malloc::dealloc(cookie as *mut u8);
        }
        Errno::ENOMEM.set();
    }
    f
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CStr;

    #[test]
    fn memstream_roundtrip() {
        let mut p: *mut c_char = ptr::null_mut();
        let mut n: usize = 0;
        // SAFETY: valid out-pointers; the stream is used correctly.
        unsafe {
            let f = open_memstream(&mut p, &mut n);
            assert!(!f.is_null());
            assert_eq!(fputs(c"hello ".as_ptr(), f), 1);
            assert_eq!(fwrite(b"world".as_ptr() as _, 1, 5, f), 5);
            assert_eq!(fflush(f), 0);
            assert_eq!(n, 11);
            assert_eq!(CStr::from_ptr(p).to_bytes(), b"hello world");
            for _ in 0..1000 {
                assert_eq!(fputc(b'x' as c_int, f), b'x' as c_int);
            }
            assert_eq!(fclose(f), 0);
            assert_eq!(n, 1011);
            assert_eq!(CStr::from_ptr(p).to_bytes().len(), 1011);
            malloc::dealloc(p as *mut u8);
        }
    }

    #[test]
    fn fmemopen_read_and_write() {
        let mut buf = *b"line one\nline two\n";
        // SAFETY: the buffer outlives the stream.
        unsafe {
            let f = fmemopen(buf.as_mut_ptr() as _, buf.len(), c"r".as_ptr());
            assert!(!f.is_null());
            let mut line = [0 as c_char; 32];
            assert!(!fgets(line.as_mut_ptr(), 32, f).is_null());
            assert_eq!(CStr::from_ptr(line.as_ptr()).to_bytes(), b"line one\n");
            assert_eq!(fgetc(f), b'l' as c_int);
            assert_eq!(ungetc(b'L' as c_int, f), b'L' as c_int);
            assert!(!fgets(line.as_mut_ptr(), 4, f).is_null());
            assert_eq!(CStr::from_ptr(line.as_ptr()).to_bytes(), b"Lin");
            assert_eq!(ftell(f), 12);
            assert_eq!(fseek(f, -3, SEEK_END), 0);
            assert!(!fgets(line.as_mut_ptr(), 32, f).is_null());
            assert_eq!(CStr::from_ptr(line.as_ptr()).to_bytes(), b"wo\n");
            assert_eq!(fgetc(f), EOF);
            assert_eq!(feof(f), 1);
            assert_eq!(fclose(f), 0);

            let mut out = [0u8; 8];
            let f = fmemopen(out.as_mut_ptr() as _, 8, c"w".as_ptr());
            assert_eq!(fputs(c"0123456789".as_ptr(), f), 1);
            assert_eq!(
                fclose(f),
                EOF,
                "the overflow is reported when the buffer is flushed"
            );
            assert_eq!(&out, b"01234567");
        }
    }

    #[test]
    fn getline_grows() {
        let mut data =
            *b"short\na much longer line that will need a bigger buffer than the first\n";
        // SAFETY: buffer outlives the stream; getline contract respected.
        unsafe {
            let f = fmemopen(data.as_mut_ptr() as _, data.len(), c"r".as_ptr());
            let mut line: *mut c_char = ptr::null_mut();
            let mut cap = 0usize;
            assert_eq!(getline(&mut line, &mut cap, f), 6);
            assert_eq!(CStr::from_ptr(line).to_bytes(), b"short\n");
            let n = getline(&mut line, &mut cap, f);
            assert_eq!(n, 65);
            assert!(cap > 65);
            assert_eq!(getline(&mut line, &mut cap, f), -1);
            malloc::dealloc(line as *mut u8);
            fclose(f);
        }
    }
}
