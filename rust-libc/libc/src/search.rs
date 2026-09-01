//! `<search.h>`: binary trees (`tsearch` & co. as a randomised treap, so
//! sorted insertion order cannot degrade it), hash tables (`hsearch`),
//! linear search and queues.

use crate::errno::Errno;
use crate::malloc;
use crate::sync::Mutex;
use core::ffi::{c_int, c_uint, c_void};
use core::ptr;

type Compar = unsafe extern "C" fn(*const c_void, *const c_void) -> c_int;

/// A tree node. The first field is the key so that a node pointer can be
/// used as `void **` by callers, as in glibc.
#[repr(C)]
struct Node {
    key: *const c_void,
    left: *mut Node,
    right: *mut Node,
    priority: u32,
}

static PRIO: Mutex<u64> = Mutex::new(0x9e37_79b9_7f4a_7c15);

fn next_priority() -> u32 {
    let mut s = PRIO.lock();
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    (*s >> 32) as u32
}

/// # Safety
/// `rootp` must point to a valid tree root; `cmp` valid.
unsafe fn insert(
    rootp: *mut *mut Node,
    key: *const c_void,
    cmp: Compar,
    prio: u32,
) -> Option<*mut Node> {
    // SAFETY: caller contract.
    unsafe {
        let node = *rootp;
        if node.is_null() {
            let n = malloc::alloc(core::mem::size_of::<Node>()) as *mut Node;
            if n.is_null() {
                return None;
            }
            n.write(Node {
                key,
                left: ptr::null_mut(),
                right: ptr::null_mut(),
                priority: prio,
            });
            *rootp = n;
            return Some(n);
        }
        let c = cmp(key, (*node).key);
        if c == 0 {
            return Some(node);
        }
        let child = if c < 0 {
            &raw mut (*node).left
        } else {
            &raw mut (*node).right
        };
        let found = insert(child, key, cmp, prio)?;
        // Rotate up to restore the heap property.
        let ch = *child;
        if (*ch).priority > (*node).priority {
            if c < 0 {
                (*node).left = (*ch).right;
                (*ch).right = node;
            } else {
                (*node).right = (*ch).left;
                (*ch).left = node;
            }
            *rootp = ch;
        }
        Some(found)
    }
}

/// `tsearch(3)`.
///
/// # Safety
/// `rootp` must point to a `void *` root (initially NULL); `cmp` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn tsearch(
    key: *const c_void,
    rootp: *mut *mut c_void,
    cmp: Compar,
) -> *mut c_void {
    if rootp.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: forwarded.
    match unsafe { insert(rootp as *mut *mut Node, key, cmp, next_priority()) } {
        Some(n) => n as *mut c_void,
        None => ptr::null_mut(),
    }
}

/// `tfind(3)`.
///
/// # Safety
/// As for [`tsearch`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn tfind(
    key: *const c_void,
    rootp: *const *mut c_void,
    cmp: Compar,
) -> *mut c_void {
    if rootp.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: caller contract.
    let mut node = unsafe { *rootp } as *mut Node;
    while !node.is_null() {
        // SAFETY: valid node.
        let c = unsafe { cmp(key, (*node).key) };
        if c == 0 {
            return node as *mut c_void;
        }
        // SAFETY: valid node.
        node = unsafe { if c < 0 { (*node).left } else { (*node).right } };
    }
    ptr::null_mut()
}

/// Removes the root of `*rootp` by merging its subtrees.
///
/// # Safety
/// `rootp` must point to a non-null node.
unsafe fn remove_root(rootp: *mut *mut Node) {
    // SAFETY: caller contract.
    unsafe {
        let node = *rootp;
        let (l, r) = ((*node).left, (*node).right);
        if l.is_null() {
            *rootp = r;
        } else if r.is_null() {
            *rootp = l;
        } else if (*l).priority > (*r).priority {
            *rootp = l;
            (*node).left = (*l).right;
            (*l).right = node;
            remove_root(&raw mut (*l).right);
        } else {
            *rootp = r;
            (*node).right = (*r).left;
            (*r).left = node;
            remove_root(&raw mut (*r).left);
        }
    }
}

/// `tdelete(3)`: returns the parent of the deleted node (or the root
/// pointer itself when the root was deleted), as glibc does.
///
/// # Safety
/// As for [`tsearch`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn tdelete(
    key: *const c_void,
    rootp: *mut *mut c_void,
    cmp: Compar,
) -> *mut c_void {
    if rootp.is_null() {
        return ptr::null_mut();
    }
    let mut link = rootp as *mut *mut Node;
    let mut parent: *mut Node = ptr::null_mut();
    loop {
        // SAFETY: caller contract; links are valid.
        let node = unsafe { *link };
        if node.is_null() {
            return ptr::null_mut();
        }
        // SAFETY: valid node.
        let c = unsafe { cmp(key, (*node).key) };
        if c == 0 {
            // SAFETY: `link` points to `node`.
            unsafe {
                remove_root(link);
                malloc::dealloc(node as *mut u8);
            }
            return if parent.is_null() {
                rootp as *mut c_void
            } else {
                parent as *mut c_void
            };
        }
        parent = node;
        // SAFETY: valid node.
        link = unsafe {
            if c < 0 {
                &raw mut (*node).left
            } else {
                &raw mut (*node).right
            }
        };
    }
}

type Action = unsafe extern "C" fn(*const c_void, c_int, c_int);

/// # Safety
/// `node` must be null or valid.
unsafe fn walk(node: *const Node, action: Action, depth: c_int) {
    if node.is_null() {
        return;
    }
    // SAFETY: caller contract. VISIT: preorder 0, postorder 1, endorder 2, leaf 3.
    unsafe {
        if (*node).left.is_null() && (*node).right.is_null() {
            action(node as *const c_void, 3, depth);
            return;
        }
        action(node as *const c_void, 0, depth);
        walk((*node).left, action, depth + 1);
        action(node as *const c_void, 1, depth);
        walk((*node).right, action, depth + 1);
        action(node as *const c_void, 2, depth);
    }
}

/// `twalk(3)`.
///
/// # Safety
/// `root` must be null or a tree root; `action` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn twalk(root: *const c_void, action: Action) {
    // SAFETY: forwarded.
    unsafe { walk(root as *const Node, action, 0) }
}

/// `tdestroy(3)`.
///
/// # Safety
/// `root` must be null or a tree root; `free_node` null or valid (null
/// is an extension: the keys are left alone).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn tdestroy(
    root: *mut c_void,
    free_node: Option<unsafe extern "C" fn(*mut c_void)>,
) {
    let node = root as *mut Node;
    if node.is_null() {
        return;
    }
    // SAFETY: valid tree.
    unsafe {
        tdestroy((*node).left as *mut c_void, free_node);
        tdestroy((*node).right as *mut c_void, free_node);
        if let Some(f) = free_node {
            f((*node).key as *mut c_void);
        }
        malloc::dealloc(node as *mut u8);
    }
}

// ---------------------------------------------------------------------
// Hash tables.

/// `ENTRY`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Entry {
    /// Key (NUL-terminated string).
    pub key: *mut crate::c_char,
    /// Value.
    pub data: *mut c_void,
}

/// `struct hsearch_data`.
#[repr(C)]
pub struct HsearchData {
    table: *mut Entry,
    size: c_uint,
    filled: c_uint,
}

struct GlobalTable(HsearchData);
// SAFETY: guarded by the mutex.
unsafe impl Send for GlobalTable {}
static GLOBAL: Mutex<GlobalTable> = Mutex::new(GlobalTable(HsearchData {
    table: ptr::null_mut(),
    size: 0,
    filled: 0,
}));

fn hash(key: &[u8]) -> u64 {
    // FNV-1a.
    key.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, &b| {
        (h ^ b as u64).wrapping_mul(0x0100_0000_01b3)
    })
}

/// `hcreate_r(3)`.
///
/// # Safety
/// `htab` must be valid and zeroed.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn hcreate_r(nel: usize, htab: *mut HsearchData) -> c_int {
    // SAFETY: caller contract.
    let h = unsafe { &mut *htab };
    if !h.table.is_null() {
        Errno::EINVAL.set();
        return 0;
    }
    let size = (nel.max(8) * 2).next_power_of_two();
    let Ok(size32) = c_uint::try_from(size) else {
        Errno::ENOMEM.set();
        return 0;
    };
    let table = malloc::alloc(size * core::mem::size_of::<Entry>()) as *mut Entry;
    if table.is_null() {
        return 0;
    }
    // SAFETY: fresh block of `size` entries.
    unsafe { ptr::write_bytes(table, 0, size) };
    h.table = table;
    h.size = size32;
    h.filled = 0;
    1
}

/// `hdestroy_r(3)`.
///
/// # Safety
/// `htab` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn hdestroy_r(htab: *mut HsearchData) {
    // SAFETY: caller contract.
    let h = unsafe { &mut *htab };
    // SAFETY: our block or null.
    unsafe { malloc::dealloc(h.table as *mut u8) };
    h.table = ptr::null_mut();
    h.size = 0;
    h.filled = 0;
}

/// `hsearch_r(3)`: `action` 0 = FIND, 1 = ENTER.
///
/// # Safety
/// `item.key` must be NUL-terminated; `retval` and `htab` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn hsearch_r(
    item: Entry,
    action: c_int,
    retval: *mut *mut Entry,
    htab: *mut HsearchData,
) -> c_int {
    // SAFETY: caller contract.
    let h = unsafe { &mut *htab };
    // SAFETY: caller contract.
    unsafe { *retval = ptr::null_mut() };
    if h.table.is_null() {
        Errno::EINVAL.set();
        return 0;
    }
    // SAFETY: caller contract.
    let key = unsafe {
        core::slice::from_raw_parts(
            item.key as *const u8,
            crate::string::search::strlen(item.key as *const u8),
        )
    };
    let mask = h.size as usize - 1;
    let mut idx = hash(key) as usize & mask;
    for _ in 0..h.size {
        // SAFETY: inside the table.
        let slot = unsafe { h.table.add(idx) };
        // SAFETY: as above.
        let existing = unsafe { (*slot).key };
        if existing.is_null() {
            if action == 0 {
                Errno::ESRCH.set();
                return 0;
            }
            if h.filled + 1 >= h.size {
                Errno::ENOMEM.set();
                return 0;
            }
            // SAFETY: as above.
            unsafe {
                *slot = item;
                *retval = slot;
            }
            h.filled += 1;
            return 1;
        }
        // SAFETY: keys are NUL-terminated.
        let ek = unsafe {
            core::slice::from_raw_parts(
                existing as *const u8,
                crate::string::search::strlen(existing as *const u8),
            )
        };
        if ek == key {
            // SAFETY: as above.
            unsafe { *retval = slot };
            return 1;
        }
        idx = (idx + 1) & mask;
    }
    Errno::ENOMEM.set();
    0
}

/// `hcreate(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn hcreate(nel: usize) -> c_int {
    let mut g = GLOBAL.lock();
    // SAFETY: the global table is valid.
    unsafe { hcreate_r(nel, &mut g.0) }
}

/// `hdestroy(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn hdestroy() {
    let mut g = GLOBAL.lock();
    // SAFETY: the global table is valid.
    unsafe { hdestroy_r(&mut g.0) }
}

/// `hsearch(3)`.
///
/// # Safety
/// `item.key` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn hsearch(item: Entry, action: c_int) -> *mut Entry {
    let mut g = GLOBAL.lock();
    let mut ret = ptr::null_mut();
    // SAFETY: forwarded.
    unsafe { hsearch_r(item, action, &mut ret, &mut g.0) };
    ret
}

// ---------------------------------------------------------------------
// Linear search and queues.

/// `lfind(3)`.
///
/// # Safety
/// `base` must hold `*nmemb` elements of `size` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn lfind(
    key: *const c_void,
    base: *const c_void,
    nmemb: *mut usize,
    size: usize,
    cmp: Compar,
) -> *mut c_void {
    // SAFETY: caller contract.
    let n = unsafe { *nmemb };
    for i in 0..n {
        // SAFETY: inside the array.
        let elem = unsafe { (base as *const u8).add(i * size) as *const c_void };
        // SAFETY: caller contract.
        if unsafe { cmp(key, elem) } == 0 {
            return elem as *mut c_void;
        }
    }
    ptr::null_mut()
}

/// `lsearch(3)`: appends the key when not found.
///
/// # Safety
/// `base` must have room for one more element.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn lsearch(
    key: *const c_void,
    base: *mut c_void,
    nmemb: *mut usize,
    size: usize,
    cmp: Compar,
) -> *mut c_void {
    // SAFETY: forwarded.
    let found = unsafe { lfind(key, base, nmemb, size, cmp) };
    if !found.is_null() {
        return found;
    }
    // SAFETY: caller contract.
    unsafe {
        let slot = (base as *mut u8).add(*nmemb * size);
        ptr::copy_nonoverlapping(key as *const u8, slot, size);
        *nmemb += 1;
        slot as *mut c_void
    }
}

#[repr(C)]
struct QNode {
    next: *mut QNode,
    prev: *mut QNode,
}

/// `insque(3)`.
///
/// # Safety
/// `elem` must be a valid queue element; `prev` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn insque(elem: *mut c_void, prev: *mut c_void) {
    let (e, p) = (elem as *mut QNode, prev as *mut QNode);
    // SAFETY: caller contract.
    unsafe {
        if p.is_null() {
            (*e).next = ptr::null_mut();
            (*e).prev = ptr::null_mut();
            return;
        }
        (*e).next = (*p).next;
        (*e).prev = p;
        if !(*p).next.is_null() {
            (*(*p).next).prev = e;
        }
        (*p).next = e;
    }
}

/// `remque(3)`.
///
/// # Safety
/// `elem` must be a valid queue element.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn remque(elem: *mut c_void) {
    let e = elem as *mut QNode;
    // SAFETY: caller contract.
    unsafe {
        if !(*e).prev.is_null() {
            (*(*e).prev).next = (*e).next;
        }
        if !(*e).next.is_null() {
            (*(*e).next).prev = (*e).prev;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    unsafe extern "C" fn cmp(a: *const c_void, b: *const c_void) -> c_int {
        // SAFETY: the test stores i64 keys.
        unsafe { (*(a as *const i64)).cmp(&*(b as *const i64)) as c_int }
    }

    #[test]
    fn treap() {
        let keys: Vec<i64> = (0..2000).collect();
        let mut root: *mut c_void = ptr::null_mut();
        // SAFETY: valid keys and root.
        unsafe {
            for k in &keys {
                let n = tsearch(k as *const i64 as *const c_void, &mut root, cmp);
                assert_eq!(*(n as *const *const i64), k as *const i64);
            }
            // Re-inserting returns the existing node.
            let n = tsearch(&keys[5] as *const i64 as *const c_void, &mut root, cmp);
            assert_eq!(*(n as *const *const i64), &keys[5] as *const i64);
            for k in &keys {
                assert!(!tfind(k as *const i64 as *const c_void, &root, cmp).is_null());
            }
            let missing = 5000i64;
            assert!(tfind(&missing as *const i64 as *const c_void, &root, cmp).is_null());
            // Depth stays logarithmic despite sorted insertion.
            fn depth(n: *const Node) -> usize {
                // SAFETY: valid tree.
                if n.is_null() {
                    0
                } else {
                    1 + unsafe { depth((*n).left).max(depth((*n).right)) }
                }
            }
            assert!(depth(root as *const Node) < 60);
            for k in keys.iter().step_by(2) {
                assert!(!tdelete(k as *const i64 as *const c_void, &mut root, cmp).is_null());
            }
            assert!(tfind(&keys[0] as *const i64 as *const c_void, &root, cmp).is_null());
            assert!(!tfind(&keys[1] as *const i64 as *const c_void, &root, cmp).is_null());
            assert!(tdelete(&missing as *const i64 as *const c_void, &mut root, cmp).is_null());
            unsafe extern "C" fn nofree(_: *mut c_void) {}
            tdestroy(root, nofree);
        }
    }

    #[test]
    fn hash_and_linear() {
        let keys: Vec<std::ffi::CString> = (0..100)
            .map(|i| std::ffi::CString::new(format!("key{i}")).unwrap())
            .collect();
        let mut table = HsearchData {
            table: ptr::null_mut(),
            size: 0,
            filled: 0,
        };
        // SAFETY: valid inputs.
        unsafe {
            assert_eq!(hcreate_r(50, &mut table), 1);
            for (i, k) in keys.iter().enumerate() {
                let mut ret = ptr::null_mut();
                assert_eq!(
                    hsearch_r(
                        Entry {
                            key: k.as_ptr() as *mut _,
                            data: i as *mut c_void
                        },
                        1,
                        &mut ret,
                        &mut table
                    ),
                    1
                );
            }
            let mut ret = ptr::null_mut();
            assert_eq!(
                hsearch_r(
                    Entry {
                        key: keys[42].as_ptr() as *mut _,
                        data: ptr::null_mut()
                    },
                    0,
                    &mut ret,
                    &mut table
                ),
                1
            );
            assert_eq!((*ret).data as usize, 42);
            let nope = c"nope";
            assert_eq!(
                hsearch_r(
                    Entry {
                        key: nope.as_ptr() as *mut _,
                        data: ptr::null_mut()
                    },
                    0,
                    &mut ret,
                    &mut table
                ),
                0
            );
            hdestroy_r(&mut table);
            let mut arr = [1i64, 5, 9, 0, 0];
            let mut n = 3usize;
            let key = 5i64;
            assert!(
                !lfind(
                    &key as *const i64 as *const c_void,
                    arr.as_ptr() as *const c_void,
                    &mut n,
                    8,
                    cmp
                )
                .is_null()
            );
            let key = 7i64;
            assert!(
                lfind(
                    &key as *const i64 as *const c_void,
                    arr.as_ptr() as *const c_void,
                    &mut n,
                    8,
                    cmp
                )
                .is_null()
            );
            lsearch(
                &key as *const i64 as *const c_void,
                arr.as_mut_ptr() as *mut c_void,
                &mut n,
                8,
                cmp,
            );
            assert_eq!(n, 4);
            assert_eq!(arr[3], 7);
        }
    }
}
