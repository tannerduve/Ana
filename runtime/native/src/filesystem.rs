//! Linux filesystem and pipe primitives. Descriptors returned to Lean are owned
//! by the Lean interpreter; descriptors accepted as arguments are borrowed.

use std::ffi::{CStr, CString};
use std::io;
use std::mem::MaybeUninit;
use std::os::fd::{AsRawFd, FromRawFd, IntoRawFd, OwnedFd, RawFd};
use std::ptr::NonNull;

fn raw_fd(fd: u32) -> io::Result<RawFd> {
    i32::try_from(fd).map_err(|_| io::Error::from_raw_os_error(libc::EBADF))
}

fn checked(result: libc::c_int) -> io::Result<()> {
    if result < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

fn descriptor(result: libc::c_int) -> io::Result<u32> {
    if result < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(result as u32)
    }
}

pub fn open_dir(path: &CStr) -> io::Result<u32> {
    // SAFETY: path is NUL-terminated and borrowed for the call; flags need no mode argument.
    descriptor(unsafe {
        libc::open(
            path.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    })
}

pub fn open_dir_at(parent: u32, name: &CStr) -> io::Result<u32> {
    // SAFETY: the OS validates the borrowed descriptor; name is a live C string.
    descriptor(unsafe {
        libc::openat(
            raw_fd(parent)?,
            name.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    })
}

pub fn open_read_at(parent: u32, name: &CStr) -> io::Result<u32> {
    // NONBLOCK prevents a special file such as a FIFO from blocking before stat rejects it.
    // SAFETY: the descriptor and C string are valid arguments to openat.
    descriptor(unsafe {
        libc::openat(
            raw_fd(parent)?,
            name.as_ptr(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
        )
    })
}

pub fn open_write_at(
    parent: u32,
    name: &CStr,
    exclusive: bool,
    append: bool,
    mode: u32,
) -> io::Result<u32> {
    let mut flags =
        libc::O_WRONLY | libc::O_CREAT | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC;
    if exclusive {
        flags |= libc::O_EXCL;
    }
    flags |= if append {
        libc::O_APPEND
    } else {
        libc::O_TRUNC
    };
    // SAFETY: O_CREAT supplies the required mode argument and name remains alive.
    descriptor(unsafe { libc::openat(raw_fd(parent)?, name.as_ptr(), flags, mode as libc::mode_t) })
}

/// Reopen stdout/stderr with an independent nonblocking open-file description.
/// Setting O_NONBLOCK on a dup would also change the shell's shared description.
pub fn open_output(fd: u32) -> io::Result<u32> {
    if !matches!(fd, 1 | 2) {
        return Err(io::Error::from_raw_os_error(libc::EINVAL));
    }
    let mut metadata = MaybeUninit::<libc::stat>::uninit();
    // SAFETY: fstat initializes metadata on success; fd is a standard descriptor.
    checked(unsafe { libc::fstat(fd as RawFd, metadata.as_mut_ptr()) })?;
    let metadata = unsafe { metadata.assume_init() };
    let kind = metadata.st_mode & libc::S_IFMT;
    // TTYs and /dev/null are supported character sinks; arbitrary devices and
    // sockets have no safe generic reopening contract here.
    if kind != libc::S_IFREG
        && kind != libc::S_IFIFO
        && !(kind == libc::S_IFCHR
            && (unsafe { libc::isatty(fd as RawFd) } == 1 || metadata.st_rdev == 0x103))
    {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "unsupported output descriptor",
        ));
    }
    // SAFETY: F_GETFL only observes the borrowed standard descriptor.
    let previous = unsafe { libc::fcntl(fd as RawFd, libc::F_GETFL) };
    checked(previous)?;
    let path = CString::new(format!("/proc/self/fd/{fd}")).expect("numeric descriptor path");
    // SAFETY: the path is live and no creation mode is needed.
    let opened = descriptor(unsafe {
        libc::open(
            path.as_ptr(),
            libc::O_WRONLY
                | libc::O_NONBLOCK
                | libc::O_CLOEXEC
                | libc::O_NOCTTY
                | (previous & libc::O_APPEND),
        )
    })?;
    // SAFETY: opened is newly owned; the guard closes it if positioning fails.
    let owned = unsafe { OwnedFd::from_raw_fd(opened as RawFd) };
    if kind == libc::S_IFREG && previous & libc::O_APPEND == 0 {
        // SAFETY: both descriptors are valid regular files; SEEK_CUR does not move fd.
        let position = unsafe { libc::lseek(fd as RawFd, 0, libc::SEEK_CUR) };
        if position < 0 {
            return Err(io::Error::last_os_error());
        }
        if unsafe { libc::lseek(owned.as_raw_fd(), position, libc::SEEK_SET) } < 0 {
            return Err(io::Error::last_os_error());
        }
    }
    Ok(owned.into_raw_fd() as u32)
}

pub fn close(fd: u32) -> io::Result<()> {
    // SAFETY: this operation consumes the descriptor owned by the caller. Do not
    // retry EINTR: Linux has already released the number, which could be reused.
    checked(unsafe { libc::close(raw_fd(fd)?) })
}

fn read_once(fd: RawFd, maximum: u64) -> io::Result<Vec<u8>> {
    if maximum > 64 * 1024 * 1024 {
        return Err(io::Error::from_raw_os_error(libc::EINVAL));
    }
    let mut bytes = vec![0; maximum as usize];
    loop {
        // SAFETY: the vector owns maximum initialized writable bytes.
        let count = unsafe { libc::read(fd, bytes.as_mut_ptr().cast(), bytes.len()) };
        if count >= 0 {
            bytes.truncate(count as usize);
            return Ok(bytes);
        }
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::Interrupted {
            return Err(error);
        }
    }
}

pub fn read(fd: u32, maximum: u64) -> io::Result<Vec<u8>> {
    read_once(raw_fd(fd)?, maximum)
}

pub fn read_available(fd: u32, maximum: u64) -> io::Result<Option<Vec<u8>>> {
    match read_once(raw_fd(fd)?, maximum) {
        Ok(bytes) => Ok(Some(bytes)),
        Err(error) if error.kind() == io::ErrorKind::WouldBlock => Ok(None),
        Err(error) => Err(error),
    }
}

pub fn write(fd: u32, bytes: &[u8]) -> io::Result<()> {
    let fd = raw_fd(fd)?;
    let mut remaining = bytes;
    while !remaining.is_empty() {
        // SAFETY: remaining is a live readable slice and libc does not retain it.
        let count = unsafe { libc::write(fd, remaining.as_ptr().cast(), remaining.len()) };
        if count < 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        if count == 0 {
            return Err(io::Error::new(
                io::ErrorKind::WriteZero,
                "write made no progress",
            ));
        }
        remaining = &remaining[count as usize..];
    }
    Ok(())
}

pub fn write_available(fd: u32, bytes: &[u8], offset: u64) -> io::Result<u64> {
    let offset = usize::try_from(offset).map_err(|_| io::Error::from_raw_os_error(libc::EINVAL))?;
    let remaining = bytes
        .get(offset..)
        .ok_or_else(|| io::Error::from_raw_os_error(libc::EINVAL))?;
    // SAFETY: remaining is valid for the length supplied, including an empty slice.
    let count = unsafe { libc::write(raw_fd(fd)?, remaining.as_ptr().cast(), remaining.len()) };
    if count >= 0 {
        return Ok(count as u64);
    }
    let error = io::Error::last_os_error();
    if matches!(
        error.kind(),
        io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
    ) {
        Ok(0)
    } else {
        Err(error)
    }
}

pub fn sync(fd: u32) -> io::Result<()> {
    // SAFETY: fsync only borrows the OS descriptor.
    checked(unsafe { libc::fsync(raw_fd(fd)?) })
}

pub fn flock(fd: u32, exclusive: bool, nonblock: bool) -> io::Result<bool> {
    let mut flags = if exclusive {
        libc::LOCK_EX
    } else {
        libc::LOCK_SH
    };
    if nonblock {
        flags |= libc::LOCK_NB;
    }
    // SAFETY: flock only borrows the OS descriptor.
    if unsafe { libc::flock(raw_fd(fd)?, flags) } == 0 {
        return Ok(true);
    }
    let error = io::Error::last_os_error();
    if nonblock && error.kind() == io::ErrorKind::WouldBlock {
        Ok(false)
    } else {
        Err(error)
    }
}

fn file_info(metadata: libc::stat) -> [u64; 6] {
    let kind = match metadata.st_mode & libc::S_IFMT {
        libc::S_IFREG => 1,
        libc::S_IFDIR => 2,
        libc::S_IFLNK => 3,
        _ => 0,
    };
    [
        kind,
        metadata.st_size as u64,
        (metadata.st_mode & 0o7777) as u64,
        metadata.st_nlink,
        metadata.st_dev,
        metadata.st_ino,
    ]
}

pub fn stat(fd: u32) -> io::Result<[u64; 6]> {
    let mut metadata = MaybeUninit::<libc::stat>::uninit();
    // SAFETY: fstat initializes stat on success; the error path never reads it.
    checked(unsafe { libc::fstat(raw_fd(fd)?, metadata.as_mut_ptr()) })?;
    Ok(file_info(unsafe { metadata.assume_init() }))
}

pub fn stat_at(parent: u32, name: &CStr) -> io::Result<[u64; 6]> {
    let mut metadata = MaybeUninit::<libc::stat>::uninit();
    // SAFETY: fstatat initializes stat on success and borrows name and parent.
    if unsafe {
        libc::fstatat(
            raw_fd(parent)?,
            name.as_ptr(),
            metadata.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } < 0
    {
        let error = io::Error::last_os_error();
        return if error.raw_os_error() == Some(libc::ENOENT) {
            Ok([4, 0, 0, 0, 0, 0])
        } else {
            Err(error)
        };
    }
    Ok(file_info(unsafe { metadata.assume_init() }))
}

pub fn read_link_at(parent: u32, name: &CStr) -> io::Result<String> {
    let mut bytes = [0u8; 4096];
    // SAFETY: name is borrowed and bytes is writable for the supplied length.
    let count = unsafe {
        libc::readlinkat(
            raw_fd(parent)?,
            name.as_ptr(),
            bytes.as_mut_ptr().cast(),
            bytes.len(),
        )
    };
    if count < 0 {
        return Err(io::Error::last_os_error());
    }
    if count as usize == bytes.len() {
        return Err(io::Error::from_raw_os_error(libc::ENAMETOOLONG));
    }
    String::from_utf8(bytes[..count as usize].to_vec())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "symlink target is not UTF-8"))
}

struct Directory(NonNull<libc::DIR>);

impl Drop for Directory {
    fn drop(&mut self) {
        // SAFETY: this guard exclusively owns the live DIR returned by fdopendir.
        unsafe {
            libc::closedir(self.0.as_ptr());
        }
    }
}

pub fn list_dir(fd: u32, limit: u32) -> io::Result<Vec<String>> {
    let copy = open_dir_at(fd, c".")?;
    // SAFETY: open_dir_at returned a fresh owned descriptor.
    let copy = unsafe { OwnedFd::from_raw_fd(copy as RawFd) };
    // SAFETY: fdopendir borrows the valid FD on failure and assumes ownership on success.
    let directory = NonNull::new(unsafe { libc::fdopendir(copy.as_raw_fd()) })
        .ok_or_else(io::Error::last_os_error)?;
    let _ = copy.into_raw_fd();
    let directory = Directory(directory);
    let mut names = Vec::new();
    loop {
        // SAFETY: errno is thread-local; readdir borrows this exclusively owned DIR.
        unsafe {
            *libc::__errno_location() = 0;
        }
        let entry = unsafe { libc::readdir(directory.0.as_ptr()) };
        if entry.is_null() {
            let error = io::Error::last_os_error();
            return if error.raw_os_error() == Some(0) {
                Ok(names)
            } else {
                Err(error)
            };
        }
        // SAFETY: readdir's name is NUL-terminated and valid until the next call.
        let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) };
        if name == c"." || name == c".." {
            continue;
        }
        if names.len() >= limit as usize {
            return Err(io::Error::from_raw_os_error(libc::EOVERFLOW));
        }
        let name = name.to_str().map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidData, "directory entry is not UTF-8")
        })?;
        names.push(name.to_owned());
    }
}

pub fn rename_at(parent: u32, old: &CStr, new_name: &CStr) -> io::Result<()> {
    let fd = raw_fd(parent)?;
    // SAFETY: both names remain alive; the OS validates the borrowed parent FD.
    checked(unsafe { libc::renameat(fd, old.as_ptr(), fd, new_name.as_ptr()) })
}

pub fn link_at(parent: u32, old: &CStr, new_name: &CStr) -> io::Result<()> {
    let fd = raw_fd(parent)?;
    // SAFETY: both names remain alive and no symlink-following flags are supplied.
    checked(unsafe { libc::linkat(fd, old.as_ptr(), fd, new_name.as_ptr(), 0) })
}

pub fn unlink_at(parent: u32, name: &CStr) -> io::Result<()> {
    // SAFETY: name remains alive and the OS validates the borrowed parent FD.
    checked(unsafe { libc::unlinkat(raw_fd(parent)?, name.as_ptr(), 0) })
}

pub fn mkdir(path: &CStr, mode: u32) -> io::Result<()> {
    // SAFETY: path remains NUL-terminated and alive for the call.
    checked(unsafe { libc::mkdir(path.as_ptr(), mode as libc::mode_t) })
}

pub fn temp_at(parent: u32, mode: u32) -> io::Result<(String, u32)> {
    let parent = raw_fd(parent)?;
    for _ in 0..16 {
        let mut random = [0u8; 12];
        let mut filled = 0;
        while filled < random.len() {
            let remaining = &mut random[filled..];
            // SAFETY: getrandom writes at most the live mutable slice length.
            let count =
                unsafe { libc::getrandom(remaining.as_mut_ptr().cast(), remaining.len(), 0) };
            if count < 0 {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            if count == 0 {
                return Err(io::Error::from_raw_os_error(libc::EIO));
            }
            filled += count as usize;
        }
        let name = format!(".harness-{}", hex(&random));
        let c_name = CString::new(name.as_bytes()).expect("hex filename has no NUL");
        // SAFETY: c_name is live and O_CREAT is supplied with a mode argument.
        let fd = unsafe {
            libc::openat(
                parent,
                c_name.as_ptr(),
                libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                mode as libc::mode_t,
            )
        };
        if fd >= 0 {
            return Ok((name, fd as u32));
        }
        let error = io::Error::last_os_error();
        if error.raw_os_error() != Some(libc::EEXIST) {
            return Err(error);
        }
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        "temporary name collisions",
    ))
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        result.push(DIGITS[(byte >> 4) as usize] as char);
        result.push(DIGITS[(byte & 15) as usize] as char);
    }
    result
}

#[link(name = "crypto")]
unsafe extern "C" {
    fn SHA256(bytes: *const u8, length: usize, output: *mut u8) -> *mut u8;
}

pub fn sha256(bytes: &[u8]) -> io::Result<String> {
    let mut hash = [0; 32];
    // SAFETY: input is live for length bytes, output owns SHA256's required 32 bytes.
    let result = unsafe { SHA256(bytes.as_ptr(), bytes.len(), hash.as_mut_ptr()) };
    if result.is_null() {
        Err(io::Error::other("SHA256 failed"))
    } else {
        Ok(hex(&hash))
    }
}

pub fn poll_readable(fd: u32, timeout_ms: u32) -> io::Result<bool> {
    let mut descriptor = libc::pollfd {
        fd: raw_fd(fd)?,
        events: libc::POLLIN,
        revents: 0,
    };
    // SAFETY: one initialized pollfd is provided; poll does not retain its address.
    let result = unsafe { libc::poll(&mut descriptor, 1, timeout_ms.min(i32::MAX as u32) as i32) };
    if result >= 0 {
        return Ok(result > 0);
    }
    let error = io::Error::last_os_error();
    if error.kind() == io::ErrorKind::Interrupted {
        Ok(false)
    } else {
        Err(error)
    }
}

pub fn open_tty() -> io::Result<u32> {
    // SAFETY: this literal is a valid C string and open needs no mode argument.
    descriptor(unsafe {
        libc::open(
            c"/dev/tty".as_ptr(),
            libc::O_RDONLY | libc::O_NONBLOCK | libc::O_CLOEXEC,
        )
    })
}
