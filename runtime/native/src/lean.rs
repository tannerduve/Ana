//! Direct bindings to the Lean 4.33.1 runtime ABI on x86_64 Linux/glibc.
//!
//! The layouts and tagged immediates below follow that release's `lean/lean.h`.
//! Its distribution enables `LEAN_MIMALLOC`; small constructors therefore use
//! the runtime's exported mimalloc allocator, not Rust's allocator. Strings,
//! arrays, IO errors, and recursive destruction use exported Lean functions.
//! Changing the Lean version, architecture, or allocator requires ABI review.
//!
//! Call these functions only from a thread initialized by the Lean runtime.
//! Every raw input is borrowed unless `Owned::from_raw` explicitly takes it.
//! Rust-owned objects must not outlive that runtime or cross threads. Returning
//! an object to Lean transfers one reference; dropping `Owned` releases one.

use std::ffi::{CStr, c_char, c_void};
use std::io;
use std::marker::PhantomData;
use std::mem::{ManuallyDrop, align_of, offset_of, size_of};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::ptr;
use std::rc::Rc;
use std::slice;
use std::sync::atomic::{AtomicI32, Ordering};

#[cfg(not(all(
    target_arch = "x86_64",
    target_os = "linux",
    target_env = "gnu",
    target_endian = "little",
    target_pointer_width = "64"
)))]
compile_error!("Lean native ABI supports only the pinned x86_64 Linux/glibc target");

/// Opaque at the FFI boundary; valid values include odd tagged immediates.
#[repr(C)]
pub struct LeanObject {
    _opaque: [u8; 0],
}

pub type LeanObj = *mut LeanObject;

// GCC/Clang on this target pack lean_object's three unsigned bitfields into
// bytes 4..8. No other C bitfield layouts are assumed.
#[repr(C)]
struct Header {
    rc: i32,
    small_size: u16,
    other: u8,
    tag: u8,
}

#[repr(C)]
struct ArrayPrefix {
    header: Header,
    size: usize,
    capacity: usize,
}

#[repr(C)]
struct StringPrefix {
    header: Header,
    size: usize,
    capacity: usize,
    length: usize,
}

const ARRAY_TAG: u8 = 246;
const BYTE_ARRAY_TAG: u8 = 248;
const STRING_TAG: u8 = 249;

const _: () = {
    assert!(size_of::<Header>() == 8);
    assert!(align_of::<Header>() == 4);
    assert!(offset_of!(Header, small_size) == 4);
    assert!(offset_of!(Header, other) == 6);
    assert!(offset_of!(Header, tag) == 7);
    assert!(size_of::<ArrayPrefix>() == 24);
    assert!(offset_of!(ArrayPrefix, size) == 8);
    assert!(offset_of!(ArrayPrefix, capacity) == 16);
    assert!(size_of::<StringPrefix>() == 32);
    assert!(offset_of!(StringPrefix, length) == 24);
    assert!(size_of::<LeanObj>() == 8);
    assert!(size_of::<AtomicI32>() == size_of::<i32>());
    assert!(align_of::<AtomicI32>() == align_of::<i32>());
};

// Cargo's unit-test executable has no Lean-generated main to supply runtime
// symbols. Production leaves resolution to Lake's existing Lean runtime link.
#[cfg_attr(test, link(name = "leanshared"))]
unsafe extern "C" {
    fn lean_alloc_object(size: usize) -> LeanObj;
    fn lean_inc_heartbeat();
    fn mi_malloc_small(size: usize) -> *mut c_void;
    fn lean_internal_panic_out_of_memory() -> !;
    fn lean_dec_ref_cold(object: LeanObj);
    fn lean_mk_string_from_bytes(bytes: *const c_char, size: usize) -> LeanObj;
    fn lean_mk_array(size: LeanObj, initial: LeanObj) -> LeanObj;
    fn lean_array_push(array: LeanObj, value: LeanObj) -> LeanObj;
    fn lean_mk_io_error_other_error(code: u32, message: LeanObj) -> LeanObj;
}

/// One owned Lean reference. This guard is deliberately neither Send nor Sync.
pub struct Owned {
    object: LeanObj,
    _thread: PhantomData<Rc<()>>,
}

impl Owned {
    /// Take ownership of one existing reference without incrementing it.
    ///
    /// # Safety
    /// `object` must be a valid Lean value with a reference transferred to this
    /// caller. It must use the pinned runtime's allocator and remain confined
    /// to this runtime thread. A borrowed argument is not an owned reference.
    pub unsafe fn from_raw(object: LeanObj) -> Self {
        assert!(!object.is_null(), "null Lean object");
        Self {
            object,
            _thread: PhantomData,
        }
    }

    #[cfg(test)]
    pub fn as_raw(&self) -> LeanObj {
        self.object
    }

    /// Transfer the reference to Lean or another documented consuming API.
    pub fn into_raw(self) -> LeanObj {
        ManuallyDrop::new(self).object
    }
}

impl Drop for Owned {
    fn drop(&mut self) {
        if is_scalar(self.object) {
            return;
        }
        // SAFETY: Owned owns a live reference. Positive RC denotes a
        // thread-local object; negative RC destruction is delegated to Lean,
        // including its atomic/sticky-count rules. Zero means persistent.
        unsafe {
            let rc = ptr::addr_of_mut!((*self.object.cast::<Header>()).rc);
            let count = (&*rc.cast::<AtomicI32>()).load(Ordering::Relaxed);
            if count > 1 {
                rc.write(count - 1);
            } else if count != 0 {
                lean_dec_ref_cold(self.object);
            }
        }
    }
}

fn is_scalar(object: LeanObj) -> bool {
    object as usize & 1 != 0
}

fn scalar(value: usize) -> Owned {
    // All callers use values <= u32::MAX, which fit the 63-bit immediate.
    unsafe { Owned::from_raw(((value << 1) | 1) as LeanObj) }
}

/// Borrow the UTF-8 payload of a Lean String, excluding its final NUL.
///
/// # Safety
/// `object` must be a live, immutable Lean String, and `'a` must not outlive
/// the caller's borrow. No returned reference may escape the native call.
pub unsafe fn string_bytes<'a>(object: LeanObj) -> &'a [u8] {
    unsafe {
        assert!(!object.is_null() && !is_scalar(object));
        let prefix = object.cast::<StringPrefix>();
        let size = ptr::addr_of!((*prefix).size).read();
        assert!(ptr::addr_of!((*prefix).header.tag).read() == STRING_TAG && size > 0);
        slice::from_raw_parts(object.cast::<u8>().add(size_of::<StringPrefix>()), size - 1)
    }
}

/// Borrow a checked UTF-8 string. The safety contract is `string_bytes`'s.
pub unsafe fn string_str<'a>(object: LeanObj) -> io::Result<&'a str> {
    std::str::from_utf8(unsafe { string_bytes(object) })
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "invalid Lean UTF-8 string"))
}

/// Borrow an OS-compatible string, rejecting interior NUL bytes.
/// The safety contract is `string_bytes`'s.
pub unsafe fn string_cstr<'a>(object: LeanObj) -> io::Result<&'a CStr> {
    let bytes = unsafe { string_bytes(object) };
    // SAFETY: Lean String has the one additional trailing NUL guaranteed by
    // the pinned runtime. Validation also rejects any earlier NUL.
    let terminated = unsafe { slice::from_raw_parts(bytes.as_ptr(), bytes.len() + 1) };
    CStr::from_bytes_with_nul(terminated)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "string contains NUL"))
}

/// Borrow a Lean ByteArray's bytes.
///
/// # Safety
/// `object` must be a live, immutable Lean ByteArray. The returned slice must
/// not outlive the caller's borrow or escape this native call.
pub unsafe fn byte_slice<'a>(object: LeanObj) -> &'a [u8] {
    unsafe {
        assert!(!object.is_null() && !is_scalar(object));
        let prefix = object.cast::<ArrayPrefix>();
        assert!(ptr::addr_of!((*prefix).header.tag).read() == BYTE_ARRAY_TAG);
        assert!(ptr::addr_of!((*prefix).header.other).read() == 1);
        slice::from_raw_parts(
            object.cast::<u8>().add(size_of::<ArrayPrefix>()),
            ptr::addr_of!((*prefix).size).read(),
        )
    }
}

/// Borrow an Array's object slots; each element is also borrowed.
///
/// # Safety
/// `object` must be a live, immutable Lean Array. The slice and any element
/// borrowed from it must not outlive the caller's borrow or the native call.
pub unsafe fn array_slice<'a>(object: LeanObj) -> &'a [LeanObj] {
    unsafe {
        assert!(!object.is_null() && !is_scalar(object));
        let prefix = object.cast::<ArrayPrefix>();
        assert!(ptr::addr_of!((*prefix).header.tag).read() == ARRAY_TAG);
        slice::from_raw_parts(
            object.cast::<u8>().add(size_of::<ArrayPrefix>()).cast(),
            ptr::addr_of!((*prefix).size).read(),
        )
    }
}

/// Return a borrowed object field from a constructor.
///
/// # Safety
/// `object` must be a live constructor with `index` in its object-field area,
/// and the returned value must not outlive the caller's borrow.
pub unsafe fn ctor_field(object: LeanObj, index: usize) -> LeanObj {
    unsafe {
        assert!(!object.is_null() && !is_scalar(object));
        let header = object.cast::<Header>();
        assert!(ptr::addr_of!((*header).tag).read() <= 243);
        assert!(index < usize::from(ptr::addr_of!((*header).other).read()));
        object
            .cast::<u8>()
            .add(size_of::<Header>())
            .cast::<LeanObj>()
            .add(index)
            .read()
    }
}

/// Inspect an Option without consuming it or its payload.
///
/// # Safety
/// `object` must be a valid Lean Option, borrowed for the entire use of the
/// returned payload. A some value must have one object field.
pub unsafe fn option_value(object: LeanObj) -> Option<LeanObj> {
    if is_scalar(object) {
        assert!(object as usize == 1, "invalid Option.none encoding");
        None
    } else {
        unsafe {
            assert!(!object.is_null());
            assert!((*object.cast::<Header>()).tag == 1);
            Some(ctor_field(object, 0))
        }
    }
}

// Only fixed, small constructor shapes are exposed. Initialize every byte so
// Lean's structural sharing routines cannot read uninitialized padding.
fn constructor(tag: u8, fields: Vec<Owned>, scalar_data: &[u8]) -> Owned {
    assert!(tag <= 243 && fields.len() < 256 && scalar_data.len() < 1024);
    let size = size_of::<Header>() + fields.len() * size_of::<LeanObj>() + scalar_data.len();
    let aligned = (size + 7) & !7;
    // SAFETY: this is lean_alloc_ctor_memory/lean_set_st_header for the pinned
    // LEAN_MIMALLOC build. Allocator, object size, and header agree with Lean's
    // destructor; all fields are initialized before ownership is published.
    unsafe {
        lean_inc_heartbeat();
        let object = mi_malloc_small(aligned).cast::<LeanObject>();
        if object.is_null() {
            lean_internal_panic_out_of_memory();
        }
        ptr::write_bytes(object.cast::<u8>(), 0, aligned);
        object.cast::<Header>().write(Header {
            rc: 1,
            small_size: aligned as u16,
            other: fields.len() as u8,
            tag,
        });
        let destination = object.cast::<u8>().add(size_of::<Header>());
        ptr::copy_nonoverlapping(
            scalar_data.as_ptr(),
            destination.add(fields.len() * size_of::<LeanObj>()),
            scalar_data.len(),
        );
        for (index, field) in fields.into_iter().enumerate() {
            destination
                .cast::<LeanObj>()
                .add(index)
                .write(field.into_raw());
        }
        Owned::from_raw(object)
    }
}

pub fn mk_unit() -> Owned {
    scalar(0)
}

pub fn mk_bool(value: bool) -> Owned {
    scalar(usize::from(value))
}

pub fn mk_u32(value: u32) -> Owned {
    scalar(value as usize)
}

/// Decode a borrowed boxed UInt32 on the pinned 64-bit Lean ABI.
///
/// # Safety
/// `value` must have the UInt32 type declared at this native boundary.
pub unsafe fn u32_value(value: LeanObj) -> u32 {
    assert!(is_scalar(value));
    u32::try_from((value as usize) >> 1).expect("boxed UInt32 exceeds its representation")
}

pub fn mk_u64(value: u64) -> Owned {
    constructor(0, Vec::new(), &value.to_ne_bytes())
}

pub fn mk_string(value: &str) -> Owned {
    // SAFETY: Lean copies exactly len bytes and builds its own terminated
    // string. The Rust source may contain NUL and stays live during the call.
    unsafe {
        Owned::from_raw(lean_mk_string_from_bytes(
            value.as_ptr().cast(),
            value.len(),
        ))
    }
}

pub fn mk_bytes(value: &[u8]) -> Owned {
    let allocation = size_of::<ArrayPrefix>()
        .checked_add(value.len())
        .expect("Lean ByteArray allocation size overflow");
    // SAFETY: mirrors lean_alloc_sarray(1, len, len), using Lean's allocator.
    // ByteArray has no child references and the entire payload is initialized.
    unsafe {
        let object = lean_alloc_object(allocation);
        object.cast::<ArrayPrefix>().write(ArrayPrefix {
            header: Header {
                rc: 1,
                small_size: 0,
                other: 1,
                tag: BYTE_ARRAY_TAG,
            },
            size: value.len(),
            capacity: value.len(),
        });
        ptr::copy_nonoverlapping(
            value.as_ptr(),
            object.cast::<u8>().add(size_of::<ArrayPrefix>()),
            value.len(),
        );
        Owned::from_raw(object)
    }
}

pub fn mk_array(values: Vec<Owned>) -> Owned {
    // SAFETY: lean_mk_array consumes its Nat size and initial element; both
    // zero immediates need no allocation/reference counting. Each push takes
    // ownership of the previous array and one element, returning one owner.
    let mut array =
        unsafe { Owned::from_raw(lean_mk_array(scalar(0).into_raw(), mk_unit().into_raw())) };
    for value in values {
        array = unsafe { Owned::from_raw(lean_array_push(array.into_raw(), value.into_raw())) };
    }
    array
}

pub fn mk_pair(first: Owned, second: Owned) -> Owned {
    constructor(0, vec![first, second], &[])
}

pub fn mk_some(value: Owned) -> Owned {
    constructor(1, vec![value], &[])
}

pub fn mk_none() -> Owned {
    scalar(0)
}

pub fn io_ok(value: Owned) -> LeanObj {
    constructor(0, vec![value], &[]).into_raw()
}

pub fn io_error(error: io::Error) -> LeanObj {
    let code = error.raw_os_error().unwrap_or(0) as u32;
    let message = mk_string(&error.to_string());
    // SAFETY: Lean's error constructor consumes the owned message string.
    let error = unsafe { Owned::from_raw(lean_mk_io_error_other_error(code, message.into_raw())) };
    constructor(1, vec![error], &[]).into_raw()
}

/// Convert expected OS errors to Lean IO errors. Never unwind through Lean.
/// An unexpected panic aborts rather than reporting an ordinary failure after
/// an external effect might have happened; the durable intent stays unresolved.
pub fn boundary(body: impl FnOnce() -> io::Result<Owned>) -> LeanObj {
    match catch_unwind(AssertUnwindSafe(|| match body() {
        Ok(value) => io_ok(value),
        Err(error) => io_error(error),
    })) {
        Ok(result) => result,
        Err(_) => std::process::abort(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn immediate_encoding_matches_pinned_64_bit_abi() {
        assert_eq!(mk_unit().as_raw() as usize, 1);
        assert_eq!(mk_none().as_raw() as usize, 1);
        assert_eq!(mk_bool(false).as_raw() as usize, 1);
        assert_eq!(mk_bool(true).as_raw() as usize, 3);
        assert_eq!(mk_u32(u32::MAX).as_raw() as usize, 0x1_ffff_ffff);
    }
}
