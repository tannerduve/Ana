//! Native primitives called directly by the Lean interpreter through the C ABI.
//! No agent decisions, model requests, or retry policies are implemented here.

mod filesystem;
mod lean;
mod process;

use lean::{LeanObj, Owned};
use std::io;

// All pointers crossing this boundary are borrowed Lean objects. The pinned Lean
// declarations in Native.lean specify their types; the Lean runtime owns them.
// Result constructors transfer one owned Lean value back to the runtime.
macro_rules! export {
    ($name:ident ($($arg:ident : $ty:ty),*) $body:block) => {
        /// # Safety
        /// Called by the pinned Lean runtime with arguments matching Native.lean.
        /// Object arguments are borrowed for this call; results transfer ownership.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name($($arg: $ty),*) -> LeanObj {
            lean::boundary(|| $body)
        }
    };
}

export!(harness_open_dir(path: LeanObj) {
    filesystem::open_dir(unsafe { lean::string_cstr(path)? }).map(lean::mk_u32)
});
export!(harness_open_dir_at(parent: u32, name: LeanObj) {
    filesystem::open_dir_at(parent, unsafe { lean::string_cstr(name)? }).map(lean::mk_u32)
});
export!(harness_open_read_at(parent: u32, name: LeanObj) {
    filesystem::open_read_at(parent, unsafe { lean::string_cstr(name)? }).map(lean::mk_u32)
});
export!(harness_open_write_at(parent: u32, name: LeanObj, exclusive: u8, append: u8, mode: u32) {
    filesystem::open_write_at(parent, unsafe { lean::string_cstr(name)? }, exclusive != 0, append != 0, mode)
        .map(lean::mk_u32)
});
export!(harness_close(fd: u32) {
    filesystem::close(fd)?;
    Ok(lean::mk_unit())
});
export!(harness_read(fd: u32, maximum: u64) {
    Ok(lean::mk_bytes(&filesystem::read(fd, maximum)?))
});
export!(harness_write(fd: u32, bytes: LeanObj) {
    filesystem::write(fd, unsafe { lean::byte_slice(bytes) })?;
    Ok(lean::mk_unit())
});
export!(harness_sync(fd: u32) {
    filesystem::sync(fd)?;
    Ok(lean::mk_unit())
});
export!(harness_flock(fd: u32, exclusive: u8, nonblock: u8) {
    filesystem::flock(fd, exclusive != 0, nonblock != 0).map(lean::mk_bool)
});
fn file_info(values: [u64; 3]) -> Owned {
    lean::mk_array(values.into_iter().map(lean::mk_u64).collect())
}
export!(harness_stat(fd: u32) {
    filesystem::stat(fd).map(file_info)
});
export!(harness_stat_at(fd: u32, name: LeanObj) {
    filesystem::stat_at(fd, unsafe { lean::string_cstr(name)? }).map(file_info)
});
export!(harness_list_dir(fd: u32, limit: u32) {
    Ok(lean::mk_array(filesystem::list_dir(fd, limit)?.iter().map(|name| lean::mk_string(name)).collect()))
});
export!(harness_rename_at(fd: u32, old: LeanObj, new_name: LeanObj) {
    filesystem::rename_at(fd, unsafe { lean::string_cstr(old)? }, unsafe { lean::string_cstr(new_name)? })?;
    Ok(lean::mk_unit())
});
export!(harness_link_at(fd: u32, old: LeanObj, new_name: LeanObj) {
    filesystem::link_at(fd, unsafe { lean::string_cstr(old)? }, unsafe { lean::string_cstr(new_name)? })?;
    Ok(lean::mk_unit())
});
export!(harness_unlink_at(fd: u32, name: LeanObj) {
    filesystem::unlink_at(fd, unsafe { lean::string_cstr(name)? })?;
    Ok(lean::mk_unit())
});
export!(harness_mkdir(path: LeanObj, mode: u32) {
    filesystem::mkdir(unsafe { lean::string_cstr(path)? }, mode)?;
    Ok(lean::mk_unit())
});
export!(harness_temp_at(parent: u32, mode: u32) {
    let (name, fd) = filesystem::temp_at(parent, mode)?;
    Ok(lean::mk_pair(lean::mk_string(&name), lean::mk_u32(fd)))
});
export!(harness_sha256(bytes: LeanObj) {
    filesystem::sha256(unsafe { lean::byte_slice(bytes) }).map(|hash| lean::mk_string(&hash))
});

unsafe fn decode_strings(value: LeanObj) -> io::Result<Vec<String>> {
    // The caller supplies Array String, borrowed for the duration of this call.
    let objects = unsafe { lean::array_slice(value) };
    if objects.len() > 4096 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "too many process arguments",
        ));
    }
    objects
        .iter()
        .map(|&object| unsafe { lean::string_str(object).map(str::to_owned) })
        .collect()
}

unsafe fn decode_environment(value: LeanObj) -> io::Result<Vec<(String, Option<String>)>> {
    let objects = unsafe { lean::array_slice(value) };
    if objects.len() > 4096 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "too many environment entries",
        ));
    }
    objects
        .iter()
        .map(|&entry| {
            let key = unsafe { lean::string_str(lean::ctor_field(entry, 0))? }.to_owned();
            let value = unsafe { lean::option_value(lean::ctor_field(entry, 1)) };
            let value = value
                .map(|object| unsafe { lean::string_str(object).map(str::to_owned) })
                .transpose()?;
            Ok((key, value))
        })
        .collect()
}

export!(harness_spawn(command: LeanObj, args: LeanObj, cwd: LeanObj, environment: LeanObj) {
    let command = unsafe { lean::string_str(command)? };
    let args = unsafe { decode_strings(args)? };
    let cwd = unsafe { lean::option_value(cwd) };
    let cwd = cwd.map(|object| unsafe { lean::string_str(object) }).transpose()?;
    let environment = unsafe { decode_environment(environment)? };
    let values = process::spawn(command, &args, cwd, &environment)?;
    Ok(lean::mk_array(values.into_iter().map(lean::mk_u32).collect()))
});
export!(harness_peek_exit(pid: u32) {
    Ok(process::peek_exit(pid)?.map_or_else(lean::mk_none, |code| lean::mk_some(lean::mk_u32(code))))
});
export!(harness_group_has_others(pid: u32) {
    process::group_has_others(pid).map(lean::mk_bool)
});
export!(harness_try_wait(pid: u32) {
    Ok(process::try_wait(pid)?.map_or_else(lean::mk_none, |code| lean::mk_some(lean::mk_u32(code))))
});
export!(harness_read_available(fd: u32, maximum: u64) {
    Ok(filesystem::read_available(fd, maximum)?.map_or_else(lean::mk_none, |bytes| lean::mk_some(lean::mk_bytes(&bytes))))
});
export!(harness_write_available(fd: u32, bytes: LeanObj, offset: u64) {
    filesystem::write_available(fd, unsafe { lean::byte_slice(bytes) }, offset).map(lean::mk_u64)
});
export!(harness_poll_readable(fd: u32, timeout: u32) {
    filesystem::poll_readable(fd, timeout).map(lean::mk_bool)
});
export!(harness_signal_group(pid: u32, signal: u32) {
    process::signal_group(pid, signal)?;
    Ok(lean::mk_unit())
});
export!(harness_group_exists(pid: u32) {
    process::group_exists(pid).map(lean::mk_bool)
});
export!(harness_open_tty() {
    filesystem::open_tty().map(lean::mk_u32)
});
export!(harness_install_signals() {
    process::install_signals()?;
    Ok(lean::mk_unit())
});
export!(harness_cancelled() {
    Ok(lean::mk_bool(process::cancelled()))
});
export!(harness_pid() {
    Ok(lean::mk_u32(process::pid()))
});
