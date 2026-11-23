import Lean

/-! Direct Rust bindings through Lean's C ABI. This module is outside the verified pure core.
Descriptors returned by open and spawn are explicitly owned. Process creation
uses Linux/glibc posix_spawn with a synchronous exec-error report; scheduling
and resource cleanup remain in Lean. -/
namespace Harness.Native

abbrev FD := UInt32

@[extern "harness_open_dir"] opaque openDir (path : @& String) : IO FD
@[extern "harness_open_dir_at"] opaque openDirAt (parent : FD) (name : @& String) : IO FD
@[extern "harness_open_read_at"] opaque openReadAt (parent : FD) (name : @& String) : IO FD
@[extern "harness_open_write_at"] opaque openWriteAt (parent : FD) (name : @& String)
  (exclusive append : Bool) (mode : UInt32) : IO FD
@[extern "harness_close"] opaque close (fd : FD) : IO Unit
/-- Owns a nonblocking stdout/stderr sink. Regular/pipe/TTY sinks are reopened;
stream sockets use per-write nonblocking flags. Inherited flags never change. -/
@[extern "harness_open_output"] opaque openOutput (standardFd : UInt32) : IO FD
@[extern "harness_read"] opaque read (fd : FD) (maxBytes : UInt64) : IO ByteArray
@[extern "harness_write"] opaque write (fd : FD) (bytes : @& ByteArray) : IO Unit
@[extern "harness_sync"] opaque sync (fd : FD) : IO Unit
@[extern "harness_flock"] opaque flock (fd : FD) (exclusive nonblock : Bool) : IO Bool
@[extern "harness_stat"] private opaque statRaw (fd : FD) : IO (Array UInt64)
@[extern "harness_stat_at"] private opaque statAtRaw (parent : FD) (name : @& String) : IO (Array UInt64)

/-- kind: 0 other, 1 regular file, 2 directory, 3 symlink, 4 missing. -/
structure FileInfo where
  kind : Nat
  size : Nat
  mode : UInt32
  links : Nat
  device : UInt64
  inode : UInt64
  deriving Repr

private def info (raw : Array UInt64) : FileInfo :=
  {kind := raw[0]!.toNat, size := raw[1]!.toNat, mode := UInt32.ofNat raw[2]!.toNat,
   links := raw[3]!.toNat, device := raw[4]!, inode := raw[5]!}
def stat (fd : FD) : IO FileInfo := info <$> statRaw fd
def statAt (fd : FD) (name : String) : IO FileInfo := info <$> statAtRaw fd name
@[extern "harness_read_link_at"] opaque readLinkAt (parent : FD) (name : @& String) : IO String

@[extern "harness_list_dir"] opaque listDir (fd : FD) (limit : UInt32) : IO (Array String)
@[extern "harness_rename_at"] opaque renameAt (parent : FD) (oldName newName : @& String) : IO Unit
@[extern "harness_link_at"] opaque linkAt (parent : FD) (oldName newName : @& String) : IO Unit
@[extern "harness_unlink_at"] opaque unlinkAt (parent : FD) (name : @& String) : IO Unit
@[extern "harness_mkdir"] opaque mkdir (path : @& String) (mode : UInt32) : IO Unit
@[extern "harness_temp_at"] opaque mkTempAt (parent : FD) (mode : UInt32) : IO (String × FD)
@[extern "harness_sha256"] opaque sha256 (data : @& ByteArray) : IO String

/-- A successful spawn owns three nonblocking parent pipe descriptors. The libc
launcher reports setup/exec errors before returning; exit 255 remains a program result. -/
structure Spawned where
  pid : UInt32
  inputFd : FD
  stdoutFd : FD
  stderrFd : FD
  deriving Repr

@[extern "harness_spawn"] private opaque spawnRaw (cmd : @& String) (args : @& Array String)
  (cwd : @& Option String) (env : @& Array (String × Option String))
  (inherited : @& Array FD) : IO (Array UInt32)

def spawn (cmd : String) (args : Array String) (cwd : Option String)
    (env : Array (String × Option String)) (inherited : Array FD := #[]) : IO Spawned := do
  let raw ← spawnRaw cmd args cwd env inherited
  return {pid := raw[0]!, inputFd := raw[1]!, stdoutFd := raw[2]!, stderrFd := raw[3]!}

/-- Owned CLOEXEC pipe with nonblocking reader; caller closes both ends.
Explicit inherited descriptors are remapped to 3 + their array index at spawn. -/
@[extern "harness_status_pipe"] opaque statusPipe : IO (FD × FD)

/-- Observe exit without reaping, keeping the leader PID/PGID unavailable for reuse. -/
@[extern "harness_peek_exit"] opaque peekExit (pid : UInt32) : IO (Option UInt32)
/-- Linux /proc membership observation. Requires a complete visible proc namespace;
incomplete scans throw. Excludes the leader and already-dead/zombie descendants. -/
@[extern "harness_group_has_others"] opaque groupHasOthers (pid : UInt32) : IO Bool
@[extern "harness_try_wait"] opaque tryWait (pid : UInt32) : IO (Option UInt32)


/-- none means would block; some empty means EOF. -/
@[extern "harness_read_available"] opaque readAvailable (fd : FD) (maxBytes : UInt64) : IO (Option ByteArray)
/-- Zero means would block. -/
@[extern "harness_write_available"] opaque writeAvailable (fd : FD) (bytes : @& ByteArray)
  (offset : UInt64) : IO UInt64
@[extern "harness_poll_readable"] opaque pollReadable (fd : FD) (timeoutMs : UInt32) : IO Bool
@[extern "harness_signal_group"] opaque signalGroup (pid signal : UInt32) : IO Unit
@[extern "harness_group_exists"] opaque groupExists (pid : UInt32) : IO Bool
@[extern "harness_open_tty"] opaque openTTY : IO FD
/-- Installs cancellation handling and disables inherited child auto-reaping.
The runtime owns waits for its children until process-group cleanup completes. -/
@[extern "harness_install_signals"] opaque installSignals : IO Unit
@[extern "harness_cancelled"] opaque isCancelled : IO Bool
@[extern "harness_pid"] opaque getPid : IO UInt32

def withFD (acquire : IO FD) (body : FD → IO α) : IO α := do
  let fd ← acquire
  try body fd finally close fd

end Harness.Native
