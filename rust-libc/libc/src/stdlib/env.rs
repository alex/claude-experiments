//! The environment: `getenv`, `setenv`, `putenv`, `unsetenv`, `clearenv`.
//!
//! `environ` is initially the kernel-provided array on the stack. The
//! first modification copies it into a `malloc`ed array that we own from
//! then on; strings added by `setenv` are `malloc`ed too, while strings
//! given to `putenv` are referenced as C requires. Because `environ` may
//! be reassigned by the program at any time, every function re-reads it.

use crate::c_char;
use crate::errno::Errno;
use crate::malloc;
use crate::start::environ;
use crate::string::mem::memcpy;
use crate::string::str::strlen;
use crate::sync::Mutex;
use core::ffi::{c_int, c_void};
use core::ptr;

/// Tracks whether `environ` currently points at an array we allocated
/// (and its capacity), so it can be grown with `realloc`.
struct Owned {
    array: *mut *mut c_char,
    capacity: usize,
}
// SAFETY: guarded by the mutex.
unsafe impl Send for Owned {}
static OWNED: Mutex<Owned> = Mutex::new(Owned {
    array: ptr::null_mut(),
    capacity: 0,
});

/// Length of the `environ` array.
///
/// # Safety
/// `environ` must be null or NULL-terminated.
unsafe fn env_len() -> usize {
    // SAFETY: caller contract.
    unsafe {
        let env = environ;
        if env.is_null() {
            return 0;
        }
        let mut n = 0;
        while !(*env.add(n)).is_null() {
            n += 1;
        }
        n
    }
}

/// Index of the entry whose name is `name` (`len` bytes).
///
/// # Safety
/// As for [`env_len`]; `name` must be valid for `len` bytes.
unsafe fn find(name: *const u8, len: usize) -> Option<usize> {
    // SAFETY: caller contract.
    unsafe {
        let env = environ;
        if env.is_null() {
            return None;
        }
        let mut i = 0;
        loop {
            let entry = *env.add(i);
            if entry.is_null() {
                return None;
            }
            let e = entry as *const u8;
            // The entry may be shorter than `name`, so compare byte by
            // byte and stop at its terminator.
            let mut k = 0;
            while k < len && *e.add(k) == *name.add(k) {
                k += 1;
            }
            if k == len && *e.add(len) == b'=' {
                return Some(i);
            }
            i += 1;
        }
    }
}

/// `getenv(3)`.
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getenv(name: *const c_char) -> *mut c_char {
    // SAFETY: forwarded.
    unsafe {
        let len = strlen(name);
        if len == 0
            || crate::string::search::memchr(
                core::slice::from_raw_parts(name as *const u8, len),
                b'=',
            )
            .is_some()
        {
            return ptr::null_mut();
        }
        match find(name as *const u8, len) {
            Some(i) => (*(environ).add(i)).add(len + 1),
            None => ptr::null_mut(),
        }
    }
}

/// Makes sure `environ` is an array we own with room for one more entry.
/// Returns the array, or null on allocation failure.
///
/// # Safety
/// The `OWNED` lock must be held.
unsafe fn ensure_owned(owned: &mut Owned) -> *mut *mut c_char {
    // SAFETY: caller contract.
    unsafe {
        let env = environ;
        let len = env_len();
        let need = len + 2;
        if !env.is_null() && env == owned.array && owned.capacity >= need {
            return env;
        }
        let capacity = need.max(owned.capacity * 2).max(16);
        let bytes = capacity * core::mem::size_of::<*mut c_char>();
        let new = if env == owned.array && !env.is_null() {
            malloc::realloc_impl(env as *mut u8, bytes)
        } else {
            let new = malloc::alloc(bytes);
            if !new.is_null() && !env.is_null() {
                memcpy(
                    new as *mut c_void,
                    env as *const c_void,
                    (len + 1) * core::mem::size_of::<*mut c_char>(),
                );
            }
            new
        } as *mut *mut c_char;
        if new.is_null() {
            return ptr::null_mut();
        }
        if env.is_null() {
            *new = ptr::null_mut();
        }
        owned.array = new;
        owned.capacity = capacity;
        environ = new;
        new
    }
}

/// Inserts or replaces the entry `string` (`name=value`) whose name has
/// `name_len` bytes. `owned_string` says whether we allocated `string`.
///
/// # Safety
/// `string` must be NUL-terminated.
unsafe fn put(string: *mut c_char, name_len: usize, owned_string: bool) -> c_int {
    let mut owned = OWNED.lock();
    // SAFETY: caller contract; lock held.
    unsafe {
        if let Some(i) = find(string as *const u8, name_len) {
            let env = environ;
            let old = *env.add(i);
            *env.add(i) = string;
            if old != string {
                free_if_ours(old);
            }
            return 0;
        }
        let env = ensure_owned(&mut owned);
        if env.is_null() {
            if owned_string {
                malloc::dealloc(string as *mut u8);
            }
            Errno::ENOMEM.set();
            return -1;
        }
        let len = env_len();
        *env.add(len) = string;
        *env.add(len + 1) = ptr::null_mut();
        0
    }
}

/// Frees `s` if it came from `setenv`. We cannot tell `setenv` strings
/// from `putenv` strings without bookkeeping, so we keep a list.
///
/// # Safety
/// `s` must be a string that was in `environ`.
unsafe fn free_if_ours(s: *mut c_char) {
    let mut list = SETENV_STRINGS.lock();
    let pos = list.iter().position(|&p| p == s as usize);
    if let Some(pos) = pos {
        list.swap_remove(pos);
        // SAFETY: we allocated it.
        unsafe { malloc::dealloc(s as *mut u8) };
    }
}

/// Strings allocated by `setenv`, so `unsetenv`/`setenv` can free them.
static SETENV_STRINGS: Mutex<PtrList> = Mutex::new(PtrList::new());

/// A tiny growable list of pointers backed by `malloc`.
struct PtrList {
    ptr: *mut usize,
    len: usize,
    cap: usize,
}
// SAFETY: guarded by the mutex.
unsafe impl Send for PtrList {}

impl PtrList {
    const fn new() -> Self {
        PtrList {
            ptr: ptr::null_mut(),
            len: 0,
            cap: 0,
        }
    }

    fn iter(&self) -> impl Iterator<Item = &usize> {
        let items: &[usize] = if self.len == 0 {
            &[]
        } else {
            // SAFETY: `ptr` is our own block with `len` initialised elements.
            unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
        };
        items.iter()
    }

    fn push(&mut self, v: usize) -> bool {
        if self.len == self.cap {
            let cap = (self.cap * 2).max(8);
            // SAFETY: `ptr` is null or our own block.
            let new = unsafe { malloc::realloc_impl(self.ptr as *mut u8, cap * 8) } as *mut usize;
            if new.is_null() {
                return false;
            }
            self.ptr = new;
            self.cap = cap;
        }
        // SAFETY: capacity allows it.
        unsafe { *self.ptr.add(self.len) = v };
        self.len += 1;
        true
    }

    fn swap_remove(&mut self, i: usize) {
        self.len -= 1;
        // SAFETY: `i < len`.
        unsafe { *self.ptr.add(i) = *self.ptr.add(self.len) };
    }
}

/// `setenv(3)`.
///
/// # Safety
/// `name` and `value` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn setenv(
    name: *const c_char,
    value: *const c_char,
    overwrite: c_int,
) -> c_int {
    // SAFETY: forwarded.
    unsafe {
        let name_len = strlen(name);
        if name_len == 0
            || crate::string::search::memchr(
                core::slice::from_raw_parts(name as *const u8, name_len),
                b'=',
            )
            .is_some()
        {
            Errno::EINVAL.set();
            return -1;
        }
        if overwrite == 0 && find(name as *const u8, name_len).is_some() {
            return 0;
        }
        let value_len = strlen(value);
        let string = malloc::alloc(name_len + 1 + value_len + 1) as *mut c_char;
        if string.is_null() {
            Errno::ENOMEM.set();
            return -1;
        }
        memcpy(string as *mut c_void, name as *const c_void, name_len);
        *string.add(name_len) = b'=' as c_char;
        memcpy(
            string.add(name_len + 1) as *mut c_void,
            value as *const c_void,
            value_len + 1,
        );
        if !SETENV_STRINGS.lock().push(string as usize) {
            malloc::dealloc(string as *mut u8);
            Errno::ENOMEM.set();
            return -1;
        }
        put(string, name_len, true)
    }
}

/// `putenv(3)`: adds `string` (of the form `name=value`) itself to the
/// environment.
///
/// # Safety
/// `string` must be NUL-terminated and outlive its presence in `environ`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn putenv(string: *mut c_char) -> c_int {
    // SAFETY: forwarded.
    unsafe {
        let len = strlen(string);
        let Some(eq) = crate::string::search::memchr(
            core::slice::from_raw_parts(string as *const u8, len),
            b'=',
        ) else {
            return unsetenv(string);
        };
        if eq == 0 {
            Errno::EINVAL.set();
            return -1;
        }
        put(string, eq, false)
    }
}

/// `unsetenv(3)`.
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn unsetenv(name: *const c_char) -> c_int {
    // SAFETY: forwarded.
    unsafe {
        let len = strlen(name);
        if len == 0
            || crate::string::search::memchr(
                core::slice::from_raw_parts(name as *const u8, len),
                b'=',
            )
            .is_some()
        {
            Errno::EINVAL.set();
            return -1;
        }
        let _guard = OWNED.lock();
        while let Some(i) = find(name as *const u8, len) {
            let env = environ;
            let old = *env.add(i);
            // Shift the tail down, including the terminating NULL.
            let mut j = i;
            loop {
                *env.add(j) = *env.add(j + 1);
                if (*env.add(j)).is_null() {
                    break;
                }
                j += 1;
            }
            free_if_ours(old);
        }
        0
    }
}

/// `clearenv(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn clearenv() -> c_int {
    let _guard = OWNED.lock();
    // SAFETY: `environ` is NULL-terminated; strings we own are freed.
    unsafe {
        let env = environ;
        if !env.is_null() {
            let mut i = 0;
            while !(*env.add(i)).is_null() {
                free_if_ours(*env.add(i));
                i += 1;
            }
            *env = ptr::null_mut();
        }
    }
    0
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::{CStr, CString};

    fn c(s: &str) -> CString {
        CString::new(s).unwrap()
    }

    fn get(name: &str) -> Option<String> {
        // SAFETY: NUL-terminated.
        let p = unsafe { getenv(c(name).as_ptr()) };
        // SAFETY: NUL-terminated.
        if p.is_null() {
            None
        } else {
            Some(unsafe { CStr::from_ptr(p) }.to_str().unwrap().to_string())
        }
    }

    #[test]
    fn environment_roundtrip() {
        // Start from the test binary's empty `environ` (our own static).
        // SAFETY: NUL-terminated inputs; single-threaded test.
        unsafe {
            assert_eq!(get("FOO"), None);
            assert_eq!(setenv(c("FOO").as_ptr(), c("bar").as_ptr(), 1), 0);
            assert_eq!(get("FOO"), Some("bar".into()));
            assert_eq!(setenv(c("FOO").as_ptr(), c("baz").as_ptr(), 0), 0);
            assert_eq!(get("FOO"), Some("bar".into()));
            assert_eq!(setenv(c("FOO").as_ptr(), c("baz").as_ptr(), 1), 0);
            assert_eq!(get("FOO"), Some("baz".into()));
            assert_eq!(setenv(c("FO=O").as_ptr(), c("x").as_ptr(), 1), -1);
            assert_eq!(setenv(c("").as_ptr(), c("x").as_ptr(), 1), -1);
            assert_eq!(get("FO"), None);
            assert_eq!(get("FOOD"), None);
            let mut s = *b"PUT=me\0";
            assert_eq!(putenv(s.as_mut_ptr() as *mut c_char), 0);
            assert_eq!(get("PUT"), Some("me".into()));
            assert_eq!(putenv(c("=x").as_ptr() as *mut c_char), -1);
            for i in 0..100 {
                let name = format!("VAR{i}");
                assert_eq!(setenv(c(&name).as_ptr(), c(&i.to_string()).as_ptr(), 1), 0);
            }
            assert_eq!(get("VAR57"), Some("57".into()));
            assert_eq!(get("FOO"), Some("baz".into()));
            assert_eq!(unsetenv(c("VAR57").as_ptr()), 0);
            assert_eq!(get("VAR57"), None);
            assert_eq!(get("VAR58"), Some("58".into()));
            assert_eq!(unsetenv(c("NOPE").as_ptr()), 0);
            assert_eq!(unsetenv(c("A=B").as_ptr()), -1);
            assert_eq!(env_len(), 101);
            // putenv without '=' removes.
            assert_eq!(putenv(c("PUT").as_ptr() as *mut c_char), 0);
            assert_eq!(get("PUT"), None);
            assert_eq!(clearenv(), 0);
            assert_eq!(env_len(), 0);
            assert_eq!(get("FOO"), None);
            assert_eq!(setenv(c("AFTER").as_ptr(), c("clear").as_ptr(), 1), 0);
            assert_eq!(get("AFTER"), Some("clear".into()));
        }
    }
}
