//! Linux process and signal primitives. Scheduling, deadlines, buffering, and
//! cleanup decisions remain in Lean. The caller exclusively owns child waits
//! and retains an exited leader until every process-group signal has been sent.

use std::ffi::{CStr, CString};
use std::fs::File;
use std::io::{self, Read};
use std::mem::MaybeUninit;
use std::os::fd::{AsRawFd, FromRawFd, IntoRawFd, OwnedFd, RawFd};
use std::ptr;
use std::sync::atomic::{AtomicBool, Ordering};

fn invalid(operation: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, operation)
}

fn context(operation: &str, error: io::Error) -> io::Error {
    io::Error::new(error.kind(), format!("{operation}: {error}"))
}

fn posix_result(operation: &str, error: libc::c_int) -> io::Result<()> {
    if error == 0 {
        Ok(())
    } else {
        Err(context(operation, io::Error::from_raw_os_error(error)))
    }
}

fn checked_pid(pid: u32) -> io::Result<libc::pid_t> {
    if pid == 0 || pid > i32::MAX as u32 {
        Err(invalid("invalid process id"))
    } else {
        Ok(pid as libc::pid_t)
    }
}

fn c_string(value: &str) -> io::Result<CString> {
    CString::new(value).map_err(|_| invalid("process argument contains NUL"))
}

fn owned_fd(fd: RawFd, operation: &str) -> io::Result<OwnedFd> {
    if fd < 0 {
        Err(context(operation, io::Error::last_os_error()))
    } else {
        // SAFETY: each caller passes a newly created descriptor, transferring its
        // unique ownership here. No descriptor is wrapped more than once.
        Ok(unsafe { OwnedFd::from_raw_fd(fd) })
    }
}

fn above_stdio(fd: OwnedFd) -> io::Result<OwnedFd> {
    if fd.as_raw_fd() >= 3 {
        return Ok(fd);
    }
    // SAFETY: fd remains open throughout fcntl; the command takes one integer.
    let copy = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 3) };
    owned_fd(copy, "duplicate process pipe")
}

fn pipe_pair() -> io::Result<(OwnedFd, OwnedFd)> {
    let mut ends = [-1; 2];
    // SAFETY: ends contains two writable descriptor slots as required by pipe2.
    if unsafe { libc::pipe2(ends.as_mut_ptr(), libc::O_CLOEXEC) } < 0 {
        return Err(context("create process pipe", io::Error::last_os_error()));
    }
    // Both descriptors must be owned before either normalization can fail.
    let read = owned_fd(ends[0], "process read pipe")?;
    let write = owned_fd(ends[1], "process write pipe")?;
    Ok((above_stdio(read)?, above_stdio(write)?))
}

fn nonblocking(fd: &OwnedFd) -> io::Result<()> {
    // SAFETY: fd is open, and both fcntl commands use their documented arguments.
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
    if flags < 0 {
        return Err(context(
            "read process pipe flags",
            io::Error::last_os_error(),
        ));
    }
    // SAFETY: same open descriptor; F_SETFL takes an integer flag set.
    if unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
        return Err(context(
            "set process pipe flags",
            io::Error::last_os_error(),
        ));
    }
    Ok(())
}

struct Actions(libc::posix_spawn_file_actions_t);

impl Actions {
    fn new() -> io::Result<Self> {
        let mut value = MaybeUninit::uninit();
        // SAFETY: libc initializes this object on a successful return.
        posix_result("initialize spawn actions", unsafe {
            libc::posix_spawn_file_actions_init(value.as_mut_ptr())
        })?;
        // SAFETY: initialization above succeeded.
        Ok(Self(unsafe { value.assume_init() }))
    }
}

impl Drop for Actions {
    fn drop(&mut self) {
        // SAFETY: this object was initialized and is destroyed exactly once.
        unsafe { libc::posix_spawn_file_actions_destroy(&mut self.0) };
    }
}

struct Attributes(libc::posix_spawnattr_t);

impl Attributes {
    fn new() -> io::Result<Self> {
        let mut value = MaybeUninit::uninit();
        // SAFETY: libc initializes this object on a successful return.
        posix_result("initialize spawn attributes", unsafe {
            libc::posix_spawnattr_init(value.as_mut_ptr())
        })?;
        // SAFETY: initialization above succeeded.
        Ok(Self(unsafe { value.assume_init() }))
    }
}

impl Drop for Attributes {
    fn drop(&mut self) {
        // SAFETY: this object was initialized and is destroyed exactly once.
        unsafe { libc::posix_spawnattr_destroy(&mut self.0) };
    }
}

fn add_chdir(actions: &mut Actions, directory: &CStr) -> io::Result<()> {
    type AddChdir = unsafe extern "C" fn(
        *mut libc::posix_spawn_file_actions_t,
        *const libc::c_char,
    ) -> libc::c_int;
    // Lean's link-time libc stub predates this GNU extension; resolve it from
    // the actual supported Linux libc, without a second C implementation.
    // SAFETY: this is a static NUL-terminated symbol name and RTLD_DEFAULT.
    let symbol = unsafe {
        libc::dlsym(
            libc::RTLD_DEFAULT,
            c"posix_spawn_file_actions_addchdir_np".as_ptr(),
        )
    };
    if symbol.is_null() {
        return Err(context(
            "spawn chdir unavailable",
            io::Error::from_raw_os_error(libc::ENOSYS),
        ));
    }
    // SAFETY: the named glibc symbol has precisely AddChdir's documented ABI.
    let function: AddChdir = unsafe { std::mem::transmute(symbol) };
    // SAFETY: actions is initialized; directory is a live NUL-terminated string.
    posix_result("add spawn chdir", unsafe {
        function(&mut actions.0, directory.as_ptr())
    })
}

fn add_closefrom(actions: &mut Actions) -> io::Result<()> {
    type AddCloseFrom =
        unsafe extern "C" fn(*mut libc::posix_spawn_file_actions_t, libc::c_int) -> libc::c_int;
    // SAFETY: static NUL-terminated symbol name and RTLD_DEFAULT.
    let symbol = unsafe {
        libc::dlsym(
            libc::RTLD_DEFAULT,
            c"posix_spawn_file_actions_addclosefrom_np".as_ptr(),
        )
    };
    if symbol.is_null() {
        return Err(context(
            "spawn closefrom unavailable",
            io::Error::from_raw_os_error(libc::ENOSYS),
        ));
    }
    // SAFETY: the named glibc symbol has precisely AddCloseFrom's documented ABI.
    let function: AddCloseFrom = unsafe { std::mem::transmute(symbol) };
    // SAFETY: actions is initialized and 3 is a valid first descriptor.
    posix_result("add spawn closefrom", unsafe {
        function(&mut actions.0, 3)
    })
}

/// Launch one process in a new session with exactly the supplied environment.
/// Success transfers the three parent pipe descriptors to Lean, in the order
/// `[pid, stdin_writer, stdout_reader, stderr_reader]`. Exec failure is an error;
/// a program's eventual exit code 255 remains an ordinary program result.
pub fn spawn(
    command: &str,
    args: &[String],
    cwd: Option<&str>,
    environment: &[(String, Option<String>)],
) -> io::Result<[u32; 4]> {
    if args.len() > 4096 || environment.len() > 4096 {
        return Err(invalid("spawn argument count exceeds 4096"));
    }
    let command = c_string(command)?;
    let args: Vec<CString> = args
        .iter()
        .map(|arg| c_string(arg))
        .collect::<io::Result<_>>()?;
    let cwd = cwd.map(c_string).transpose()?;
    let mut env = Vec::with_capacity(environment.len());
    for (key, value) in environment {
        if let Some(value) = value {
            if key.is_empty() || key.contains('=') {
                return Err(invalid("invalid process environment key"));
            }
            env.push(c_string(&format!("{key}={value}"))?);
        }
    }
    let mut argv: Vec<*mut libc::c_char> = std::iter::once(&command)
        .chain(args.iter())
        .map(|value| value.as_ptr().cast_mut())
        .collect();
    argv.push(ptr::null_mut());
    let mut envp: Vec<*mut libc::c_char> =
        env.iter().map(|value| value.as_ptr().cast_mut()).collect();
    envp.push(ptr::null_mut());

    let (input_read, input_write) = pipe_pair()?;
    let (output_read, output_write) = pipe_pair()?;
    let (error_read, error_write) = pipe_pair()?;
    nonblocking(&input_write)?;
    nonblocking(&output_read)?;
    nonblocking(&error_read)?;
    let mut actions = Actions::new()?;
    let mut attributes = Attributes::new()?;
    if let Some(directory) = &cwd {
        add_chdir(&mut actions, directory)?;
    }
    for (source, target) in [
        (input_read.as_raw_fd(), libc::STDIN_FILENO),
        (output_write.as_raw_fd(), libc::STDOUT_FILENO),
        (error_write.as_raw_fd(), libc::STDERR_FILENO),
    ] {
        // SAFETY: actions is initialized; source remains open until spawn returns.
        posix_result("add spawn dup2", unsafe {
            libc::posix_spawn_file_actions_adddup2(&mut actions.0, source, target)
        })?;
    }
    // All owned pipe descriptors are >=3, so these cannot close a dup2 target.
    for fd in [
        &input_read,
        &input_write,
        &output_read,
        &output_write,
        &error_read,
        &error_write,
    ] {
        // SAFETY: actions is initialized and fd is a valid open descriptor.
        posix_result("add spawn close", unsafe {
            libc::posix_spawn_file_actions_addclose(&mut actions.0, fd.as_raw_fd())
        })?;
    }
    add_closefrom(&mut actions)?;

    // SAFETY: sigset_t is a libc POD type, initialized by sigemptyset before use.
    let mut mask: libc::sigset_t = unsafe { std::mem::zeroed() };
    // SAFETY: same argument as mask.
    let mut defaults: libc::sigset_t = unsafe { std::mem::zeroed() };
    // SAFETY: these point to valid writable sigset_t objects; all signals are valid.
    unsafe {
        libc::sigemptyset(&mut mask);
        libc::sigemptyset(&mut defaults);
        libc::sigaddset(&mut defaults, libc::SIGINT);
        libc::sigaddset(&mut defaults, libc::SIGTERM);
        libc::sigaddset(&mut defaults, libc::SIGPIPE);
    }
    // SAFETY: initialized attributes and signal sets, valid Linux spawn flags.
    unsafe {
        posix_result(
            "set spawn signal mask",
            libc::posix_spawnattr_setsigmask(&mut attributes.0, &mask),
        )?;
        posix_result(
            "set spawn signal defaults",
            libc::posix_spawnattr_setsigdefault(&mut attributes.0, &defaults),
        )?;
        posix_result(
            "set spawn session",
            libc::posix_spawnattr_setflags(
                &mut attributes.0,
                (libc::POSIX_SPAWN_SETSID as libc::c_int
                    | libc::POSIX_SPAWN_SETSIGMASK
                    | libc::POSIX_SPAWN_SETSIGDEF) as libc::c_short,
            ),
        )?;
    }
    let mut child: libc::pid_t = 0;
    // SAFETY: all strings, pointer arrays (including their null terminators),
    // actions, attributes, and descriptor sources remain alive through spawn.
    // libc does not modify the bytes of argv/envp despite their C pointer type.
    posix_result("posix_spawn", unsafe {
        libc::posix_spawnp(
            &mut child,
            command.as_ptr(),
            &actions.0,
            &attributes.0,
            argv.as_ptr(),
            envp.as_ptr(),
        )
    })?;

    // No fallible work follows process creation. Child-side ends and spawn
    // resources drop locally; only the parent-side descriptors transfer to Lean.
    Ok([
        child as u32,
        input_write.into_raw_fd() as u32,
        output_read.into_raw_fd() as u32,
        error_read.into_raw_fd() as u32,
    ])
}

/// Observe without reaping, retaining the leader identity against PID reuse.
pub fn peek_exit(pid: u32) -> io::Result<Option<u32>> {
    let pid = checked_pid(pid)?;
    // SAFETY: siginfo_t is libc POD; waitid writes its documented fields.
    let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
    loop {
        // SAFETY: info is writable; pid and wait flags are valid.
        let result = unsafe {
            libc::waitid(
                libc::P_PID,
                pid as libc::id_t,
                &mut info,
                libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
            )
        };
        if result == 0 {
            break;
        }
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::Interrupted {
            return Err(context("waitid", error));
        }
    }
    // SAFETY: successful waitid with WEXITED initialized the child-status union.
    if unsafe { info.si_pid() } == 0 {
        return Ok(None);
    }
    // SAFETY: same successful child-status observation.
    let status = unsafe { info.si_status() } as u32;
    Ok(Some(if info.si_code == libc::CLD_EXITED {
        status
    } else {
        128 + status
    }))
}

/// Reap only after the caller has finished every process-group signal.
pub fn try_wait(pid: u32) -> io::Result<Option<u32>> {
    let pid = checked_pid(pid)?;
    let mut status = 0;
    let result = loop {
        // SAFETY: status is writable and pid identifies the caller's child.
        let result = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
        if result >= 0 {
            break result;
        }
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::Interrupted {
            return Err(context("waitpid", error));
        }
    };
    if result == 0 {
        Ok(None)
    } else if libc::WIFEXITED(status) {
        Ok(Some(libc::WEXITSTATUS(status) as u32))
    } else if libc::WIFSIGNALED(status) {
        Ok(Some((128 + libc::WTERMSIG(status)) as u32))
    } else {
        Ok(None)
    }
}

struct Directory(*mut libc::DIR);

impl Drop for Directory {
    fn drop(&mut self) {
        // SAFETY: this non-null DIR was opened successfully and is uniquely owned.
        unsafe { libc::closedir(self.0) };
    }
}

fn decimal_pid(bytes: &[u8]) -> Option<(u32, usize)> {
    let mut value = 0u32;
    let mut count = 0;
    for &byte in bytes {
        if !byte.is_ascii_digit() {
            break;
        }
        value = value.checked_mul(10)?.checked_add((byte - b'0') as u32)?;
        if value > i32::MAX as u32 {
            return None;
        }
        count += 1;
    }
    (count != 0).then_some((value, count))
}

fn group_from_stat(bytes: &[u8]) -> Option<(u8, u32)> {
    let closing = bytes.iter().rposition(|&byte| byte == b')')?;
    let rest = bytes.get(closing + 1..)?;
    if rest.first() != Some(&b' ') || rest.get(2) != Some(&b' ') {
        return None;
    }
    let state = *rest.get(1)?;
    if state == 0 {
        return None;
    }
    let (_, parent_end) = decimal_pid(rest.get(3..)?)?;
    let rest = rest.get(3 + parent_end..)?;
    if rest.first() != Some(&b' ') {
        return None;
    }
    let (group, group_end) = decimal_pid(rest.get(1..)?)?;
    if rest.get(group_end + 1) != Some(&b' ') {
        return None;
    }
    Some((state, group))
}

fn vanished(error: &io::Error) -> bool {
    matches!(error.raw_os_error(), Some(libc::ENOENT | libc::ESRCH))
}

/// Bounded, conservative procfs observation of live members other than the
/// held leader. It is not atomic against forking and cannot contain detached
/// descendants. Incomplete or unreadable observations fail rather than report
/// an empty group. The caller must own a complete Linux proc namespace.
pub fn group_has_others(pid: u32) -> io::Result<bool> {
    checked_pid(pid)?;
    // SAFETY: static NUL-terminated path; opendir returns a uniquely owned DIR.
    let raw = unsafe { libc::opendir(c"/proc".as_ptr()) };
    if raw.is_null() {
        return Err(context("open /proc", io::Error::last_os_error()));
    }
    let directory = Directory(raw);
    for visited in 0..100_001 {
        // SAFETY: errno is this thread's libc slot; DIR stays alive throughout
        // readdir, and no second thread accesses this Directory.
        let entry = unsafe {
            *libc::__errno_location() = 0;
            libc::readdir(directory.0)
        };
        if entry.is_null() {
            let error = io::Error::last_os_error();
            return if error.raw_os_error() == Some(0) {
                Ok(false)
            } else {
                Err(context("inspect process group", error))
            };
        }
        if visited == 100_000 {
            return Err(context(
                "process group entry limit",
                io::Error::from_raw_os_error(libc::EOVERFLOW),
            ));
        }
        // SAFETY: readdir supplied a live dirent with NUL-terminated d_name;
        // its bytes are consumed before the next call to readdir.
        let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
        let Some((candidate, length)) = decimal_pid(name) else {
            continue;
        };
        if length != name.len() || candidate == 0 || candidate == pid {
            continue;
        }
        // Formatted decimal numbers cannot contain NUL.
        let path = c_string(&format!("{candidate}/stat"))?;
        // SAFETY: directory is live; relative path is a valid CString; flags
        // need no mode argument and the returned descriptor is uniquely owned.
        let fd = unsafe {
            libc::openat(
                libc::dirfd(directory.0),
                path.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW,
            )
        };
        if fd < 0 {
            let error = io::Error::last_os_error();
            if vanished(&error) {
                continue;
            }
            return Err(context("inspect process group", error));
        }
        let mut file = File::from(owned_fd(fd, "open process stat")?);
        let mut data = [0; 4095];
        let size = loop {
            match file.read(&mut data) {
                Ok(size) => break Some(size),
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) if vanished(&error) => break None,
                Err(error) => return Err(context("read process stat", error)),
            }
        };
        let Some(size) = size else { continue };
        if size == 0 || size == data.len() {
            return Err(context(
                "process stat size",
                io::Error::from_raw_os_error(libc::EOVERFLOW),
            ));
        }
        let (state, group) = group_from_stat(&data[..size]).ok_or_else(|| {
            context(
                "parse process stat",
                io::Error::from_raw_os_error(libc::EPROTO),
            )
        })?;
        if group == pid && !matches!(state, b'Z' | b'X' | b'x') {
            return Ok(true);
        }
    }
    Err(context(
        "process group entry limit",
        io::Error::from_raw_os_error(libc::EOVERFLOW),
    ))
}

pub fn signal_group(pid: u32, signal: u32) -> io::Result<()> {
    let pid = checked_pid(pid)?;
    if signal > i32::MAX as u32 {
        return Err(invalid("invalid signal number"));
    }
    // SAFETY: negating a checked positive pid is defined and targets its group.
    if unsafe { libc::kill(-pid, signal as libc::c_int) } < 0 {
        let error = io::Error::last_os_error();
        if error.raw_os_error() != Some(libc::ESRCH) {
            return Err(context("kill process group", error));
        }
    }
    Ok(())
}

pub fn group_exists(pid: u32) -> io::Result<bool> {
    let pid = checked_pid(pid)?;
    // SAFETY: signal zero probes the checked process group without sending one.
    if unsafe { libc::kill(-pid, 0) } == 0 {
        return Ok(true);
    }
    let error = io::Error::last_os_error();
    match error.raw_os_error() {
        Some(libc::EPERM) => Ok(true),
        Some(libc::ESRCH) => Ok(false),
        _ => Err(context("probe process group", error)),
    }
}

static CANCELLED: AtomicBool = AtomicBool::new(false);

extern "C" fn cancel_signal(_: libc::c_int) {
    // AtomicBool's store is lock-free on the supported Linux target; this
    // handler allocates nothing and calls no non-signal-safe runtime function.
    CANCELLED.store(true, Ordering::Relaxed);
}

fn set_handler(signal: libc::c_int, handler: libc::sighandler_t) -> io::Result<()> {
    // SAFETY: sigaction is libc POD; zero flags clear inherited SA_NOCLDWAIT.
    let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
    action.sa_sigaction = handler;
    // SAFETY: valid writable action, valid signal, and no previous-action output.
    unsafe {
        libc::sigemptyset(&mut action.sa_mask);
        if libc::sigaction(signal, &action, ptr::null_mut()) < 0 {
            return Err(context(
                "install signal handler",
                io::Error::last_os_error(),
            ));
        }
    }
    Ok(())
}

/// The runtime exclusively owns waits for spawned children. Reset inherited
/// SIGCHLD auto-reaping so an exited leader continues to pin its process id.
pub fn install_signals() -> io::Result<()> {
    set_handler(libc::SIGCHLD, libc::SIG_DFL)?;
    set_handler(
        libc::SIGINT,
        cancel_signal as *const () as libc::sighandler_t,
    )?;
    set_handler(
        libc::SIGTERM,
        cancel_signal as *const () as libc::sighandler_t,
    )?;
    set_handler(libc::SIGPIPE, libc::SIG_IGN)
}

pub fn cancelled() -> bool {
    CANCELLED.load(Ordering::Relaxed)
}

pub fn pid() -> u32 {
    // SAFETY: getpid has no pointer arguments or preconditions and cannot fail.
    unsafe { libc::getpid() as u32 }
}
