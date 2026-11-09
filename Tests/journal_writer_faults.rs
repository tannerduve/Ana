//! Test-only syscall faults. Arm only on a marked frame in the exact test journal.
//! The product has no fault switches. Other files and stdout use the real syscalls.
use std::ffi::{c_char, c_int, c_void, CStr};
use std::sync::atomic::{AtomicI32, Ordering};

extern "C" {
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
    fn getenv(name: *const c_char) -> *mut c_char;
    fn readlink(path: *const c_char, buffer: *mut c_char, size: usize) -> isize;
    fn __errno_location() -> *mut c_int;
    fn _exit(code: c_int) -> !;
}

static ARMED: AtomicI32 = AtomicI32::new(0);
static TARGET: AtomicI32 = AtomicI32::new(-1);
static MATCHES: AtomicI32 = AtomicI32::new(0);

unsafe fn environment(name: &[u8]) -> &'static [u8] {
    let value = getenv(name.as_ptr().cast());
    if value.is_null() { b"" } else { CStr::from_ptr(value).to_bytes() }
}

unsafe fn matches(fd: c_int, directory: bool) -> bool {
    let expected = environment(b"HARNESS_JOURNAL_PATH\0");
    if expected.is_empty() { return false; }
    let expected = if directory {
        let Some(end) = expected.iter().rposition(|byte| *byte == b'/') else { return false; };
        &expected[..end]
    } else { expected };
    let path = format!("/proc/self/fd/{fd}\0");
    let mut buffer = [0u8; 4096];
    let count = readlink(path.as_ptr().cast(), buffer.as_mut_ptr().cast(), buffer.len());
    count >= 0 && &buffer[..count as usize] == expected
}

#[no_mangle]
pub unsafe extern "C" fn write(fd: c_int, data: *const c_void, size: usize) -> isize {
    let real: unsafe extern "C" fn(c_int, *const c_void, usize) -> isize =
        std::mem::transmute(dlsym((-1isize) as *mut c_void, b"write\0".as_ptr().cast()));
    if ARMED.load(Ordering::SeqCst) == 2 && fd == TARGET.load(Ordering::SeqCst) {
        *__errno_location() = 28; // ENOSPC
        return -1;
    }
    let mode = environment(b"HARNESS_JOURNAL_FAULT\0");
    let requested = environment(b"HARNESS_JOURNAL_MATCH\0");
    let marker = if requested.is_empty() { b"\"faultTarget\"".as_slice() } else { requested };
    if ARMED.load(Ordering::SeqCst) == 0 && matches(fd, false) && size > 0 &&
        std::slice::from_raw_parts(data.cast::<u8>(), size).windows(marker.len())
            .any(|window| window == marker) {
        let skip = std::str::from_utf8(environment(b"HARNESS_JOURNAL_SKIP\0"))
            .ok().and_then(|value| value.parse::<i32>().ok()).unwrap_or(0);
        if MATCHES.fetch_add(1, Ordering::SeqCst) < skip { return real(fd, data, size); }
        ARMED.store(1, Ordering::SeqCst);
        TARGET.store(fd, Ordering::SeqCst);
        if mode == b"crash_before_write" { _exit(88); }
        if mode == b"before_write" {
            *__errno_location() = 28;
            return -1;
        }
        if mode == b"partial" || mode == b"crash_partial" {
            let result = real(fd, data, size / 2);
            if mode == b"crash_partial" { _exit(86); }
            ARMED.store(2, Ordering::SeqCst);
            return result;
        }
    }
    real(fd, data, size)
}

#[no_mangle]
pub unsafe extern "C" fn fsync(fd: c_int) -> c_int {
    let real: unsafe extern "C" fn(c_int) -> c_int =
        std::mem::transmute(dlsym((-1isize) as *mut c_void, b"fsync\0".as_ptr().cast()));
    let mode = environment(b"HARNESS_JOURNAL_FAULT\0");
    if ARMED.load(Ordering::SeqCst) != 0 {
        if (mode == b"file_sync" && fd == TARGET.load(Ordering::SeqCst)) ||
            (mode == b"directory_sync" && matches(fd, true)) {
            *__errno_location() = 5; // EIO
            return -1;
        }
        if mode == b"crash_after_sync" && matches(fd, true) {
            let result = real(fd);
            if result == 0 { _exit(87); }
            return result;
        }
    }
    real(fd)
}

#[no_mangle]
pub unsafe extern "C" fn read(fd: c_int, data: *mut c_void, size: usize) -> isize {
    let real: unsafe extern "C" fn(c_int, *mut c_void, usize) -> isize =
        std::mem::transmute(dlsym((-1isize) as *mut c_void, b"read\0".as_ptr().cast()));
    if ARMED.load(Ordering::SeqCst) != 0 &&
        environment(b"HARNESS_JOURNAL_FAULT\0") == b"no_reads" && matches(fd, false) {
        *__errno_location() = 5;
        return -1;
    }
    real(fd, data, size)
}
