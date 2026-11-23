import Harness.Adapter.FilesystemIO

/-! Fixed bubblewrap profile preparation. The core selects the frozen profile;
this adapter validates its OS prerequisites and prepares one command. Workspace
setup assumes one writer. No credential, session or ambient environment mount is
added. Open mount descriptors remain owned here until command supervision ends. -/
namespace Harness.Sandbox
open Native

private def systemMounts : Array (String × String) :=
  #[("/usr", "/usr"), ("/lib", "/lib"), ("/lib64", "/lib64")]

private def parts (path : String) : List String :=
  (path.splitOn "/").filter (fun p => !p.isEmpty && p != ".")

private def containsPath (parent child : String) : Bool :=
  (parts parent).isPrefixOf (parts child)

private def overlaps (a b : String) : Bool := containsPath a b || containsPath b a

private def canonical (path : String) : IO String := do
  if !path.startsWith "/" || path.contains '\x00' || path.utf8ByteSize > 4096 then
    throw <| IO.userError "sandbox paths must be bounded absolute paths"
  let resolved ← IO.FS.realPath path
  unless (← resolved.metadata).type == .dir do throw <| IO.userError "sandbox mount must be a directory"
  return resolved.toString

private def homePath : IO (Option String) := do
  match ← IO.getEnv "HOME" with
  | none => pure none
  | some home => try return some (← canonical home) catch _ => return none

/-- All source contents are shared read-only; operator-supplied roots must be
clean installation trees. Their destinations and PATH ordering are fixed. -/
def mountSources (workspace session : String) (roots : Array String) : IO (Array (String × String)) := do
  if roots.size > 8 then throw <| IO.userError "sandbox supports at most eight toolchain roots"
  let actual ← canonical workspace
  unless actual == workspace do throw <| IO.userError "workspace must retain its canonical identity"
  if (workspace != "/workspace" && overlaps workspace "/workspace") ||
      ["/etc", "/proc", "/dev", "/tmp/home", "/opt/harness/toolchains"].any (overlaps workspace) then
    throw <| IO.userError "canonical workspace conflicts with reserved sandbox paths"
  if overlaps workspace session then throw <| IO.userError "workspace and session overlap"
  let home ← homePath
  if home.any (containsPath workspace) then throw <| IO.userError "sandbox workspace must not contain the host home directory"
  let mut mounts := #[]
  for (source, destination) in systemMounts do
    let source ← canonical source
    if overlaps source workspace || overlaps source session then
      throw <| IO.userError "system runtime mount overlaps workspace or session storage"
    mounts := mounts.push (source, destination)
  let mut chosen : Array String := #[]
  for index in [:roots.size] do
    let source := roots[index]!
    let actual ← canonical source
    unless actual == source do throw <| IO.userError s!"toolchain root must be canonical: {actual}"
    if source == "/" || overlaps source workspace || overlaps source session ||
        home.any (containsPath source) || chosen.any (overlaps source) then
      throw <| IO.userError "toolchain root overlaps private data, workspace, or another root"
    -- An installation prefix is explicit, not an arbitrary general-purpose mount.
    withFD (openDir source) fun fd => withFD (openDirAt fd "bin") fun _ => pure ()
    mounts := mounts.push (source, s!"/opt/harness/toolchains/{index}")
    chosen := chosen.push source
  return mounts

private def normalizeRelative (base : List String) : List String → Option (List String)
  | [] => some base
  | "" :: rest | "." :: rest => normalizeRelative base rest
  | ".." :: rest => if base.isEmpty then none else normalizeRelative base.dropLast rest
  | part :: rest => normalizeRelative (base ++ [part]) rest

private def safeLink (workspace : String) (parent : List String) (target : String) : Bool :=
  if target.isEmpty || target.contains '\x00' then false
  else if target.startsWith "/" then
    match normalizeRelative [] (target.splitOn "/") with
    | none => false
    | some resolved => (parts workspace).isPrefixOf resolved || ["workspace", "usr", "bin", "lib", "lib64"].any
        (fun root => [root].isPrefixOf resolved) ||
        ["opt", "harness", "toolchains"].isPrefixOf resolved
  else (normalizeRelative parent (target.splitOn "/")).isSome

private def checkActive (deadline : Nat) : IO Unit := do
  if (← Native.isCancelled) || (← IO.monoMsNow) ≥ deadline then
    throw <| IO.userError "sandbox validation cancelled or exceeded its deadline"

private def scan (workspace : String) (fd : FD) (path : List String) (seen : IO.Ref Nat) (deadline : Nat) : Nat → IO Unit
  | 0 => throw <| IO.userError "sandbox workspace nesting exceeds 128 directories"
  | depth + 1 => do
    checkActive deadline
    let names ← listDir fd (UInt32.ofNat (200000 - (← seen.get)))
    seen.modify (· + names.size)
    for name in names.qsort (· < ·) do
      checkActive deadline
      let info ← statAt fd name
      let label := String.intercalate "/" (path ++ [name])
      if info.kind == 1 then
        if info.links != 1 then throw <| IO.userError s!"workspace hardlink is unsupported: {label}"
        if path.isEmpty && name == ".git" then
          throw <| IO.userError "isolated workspace requires local .git directory metadata, not a linked worktree"
      else if info.kind == 2 then
        withFD (openDirAt fd name) fun child => scan workspace child (path ++ [name]) seen deadline depth
      else if info.kind == 3 then
        let target ← readLinkAt fd name
        unless safeLink workspace path target do throw <| IO.userError s!"escaping workspace symlink: {label}"
        if path.isEmpty && name == ".git" then
          throw <| IO.userError "isolated workspace requires a real local .git directory"
      else throw <| IO.userError s!"workspace contains a special or changing file: {label}"

/-- Full initial/resume scan. Later dispatch uses the same root under the
single-writer and completely-settled-previous-sandbox assumptions. -/
def validateWorkspace (workspace : String) (timeoutMs : Nat) : IO Unit := do
  let deadline := (← IO.monoMsNow) + timeoutMs
  let seen ← IO.mkRef 0
  withFD (openDir workspace) fun fd => scan workspace fd [] seen deadline 129

structure Plan where
  args : Array String
  inherited : Array FD

private structure Mount where
  source : String
  destination : String
  readOnly : Bool
  deriving Inhabited

private def resourceSources (ctx : ToolContext) (session : String)
    (base : Array (String × String)) : IO (Array Mount) := do
  unless ctx.resourceMounts.size ≤ 16 do throw <| IO.userError "too many application resource mounts"
  let home ← homePath
  let mut result := base.map fun (source, destination) => {source, destination, readOnly := true : Mount}
  let mut names : Array String := #[]
  for resource in ctx.resourceMounts do
    unless !resource.name.isEmpty && resource.name.length ≤ 64 && resource.name.toList.all
        (fun character => character.isAlphanum || character == '-' || character == '_') &&
        !names.contains resource.name do throw <| IO.userError "invalid or duplicate application resource mount"
    let source ← canonical resource.path
    unless source == resource.path do throw <| IO.userError "application resource must retain its canonical identity"
    if source == "/" || overlaps source ctx.workspace || overlaps source session ||
        home.any (containsPath source) || result.any (fun previous => overlaps previous.source source) then
      throw <| IO.userError "application resource overlaps private storage, workspace, or another mount"
    names := names.push resource.name
    result := result.push {source, destination := s!"/opt/harness/resources/{resource.name}", readOnly := resource.readOnly}
  return result

private def withDirectories (sources : List String) (owned : Array FD)
    (body : Array FD → IO α) : IO α :=
  match sources with
  | [] => body owned
  | source :: rest => withFD (openDir source) fun fd =>
      withDirectories rest (owned.push fd) body

/-- Small fixed configuration data is completely written before launch. Closing
both ends on every path avoids retaining a writer that could stall bubblewrap. -/
private def withDataFD (text : String) (body : FD → IO α) : IO α := do
  let bytes := text.toUTF8
  if bytes.size > 512 then throw <| IO.userError "sandbox configuration exceeds fixed pipe bound"
  let (reader, writer) ← statusPipe
  try
    withFD (pure writer) fun fd => Native.write fd bytes
    body reader
  finally
    Native.close reader

/-- No arbitrary flags or mount destinations are accepted. Setup descriptors are
remapped to 3 + index by Native.spawn and consumed/closed by bubblewrap. -/
def withPlan (ctx : ToolContext) (args : ProcessArgs) (statusWriter : FD)
    (body : Plan → IO α) : IO α := do
  let session := ((System.FilePath.mk ctx.artifactDir).parent.getD ".").toString
  let base ← mountSources ctx.workspace session ctx.toolchainRoots
  let mounts ← resourceSources ctx session base
  withDataFD "127.0.0.1 localhost\n::1 localhost\n" fun hosts =>
  withDataFD "hosts: files\n" fun nsswitch =>
  FilesystemIO.withWorkspaceDir ctx.workspace args.cwd fun _ =>
    withDirectories (ctx.workspace :: mounts.toList.map (·.source)) #[] fun descriptors => do
      let workspaceInfo ← Native.stat descriptors[0]!
      for fd in descriptors.extract 1 descriptors.size do
        let info ← Native.stat fd
        if info.device == workspaceInfo.device && info.inode == workspaceInfo.inode then
          throw <| IO.userError "application mount aliases the workspace"
      let toolPaths := (List.range ctx.toolchainRoots.size).map
        (fun index => s!"/opt/harness/toolchains/{index}/bin")
      let path := String.intercalate ":" (toolPaths ++ ["/usr/bin", "/bin"])
      let mut flags := #["--unshare-user", "--unshare-ipc", "--unshare-pid", "--unshare-net",
        "--unshare-uts", "--die-with-parent", "--disable-userns", "--cap-drop", "ALL",
        "--clearenv", "--setenv", "HOME", "/tmp/home", "--setenv", "TMPDIR", "/tmp",
        "--setenv", "PATH", path, "--setenv", "LANG", "C.UTF-8"]
      for index in [:mounts.size] do
        flags := flags ++ #[if mounts[index]!.readOnly then "--ro-bind-fd" else "--bind-fd",
          toString (4 + index), mounts[index]!.destination]
      let mut inherited := descriptors
      flags := flags ++ #["--dir", "/etc", "--ro-bind-data", toString (3 + inherited.size), "/etc/hosts"]
      inherited := inherited.push hosts
      flags := flags ++ #["--ro-bind-data", toString (3 + inherited.size), "/etc/nsswitch.conf"]
      inherited := inherited.push nsswitch
      let workspaceBind := if ctx.workspaceReadOnly then "--ro-bind-fd" else "--bind-fd"
      flags := flags ++ #["--symlink", "usr/bin", "/bin", "--proc", "/proc", "--dev", "/dev",
        "--tmpfs", "/tmp", "--dir", "/tmp/home", workspaceBind, "3", "/workspace"]
      -- Mount after private base filesystems, so /tmp workspaces remain visible.
      -- A second setup FD refers to the same open root; bwrap consumes each FD.
      if ctx.workspace != "/workspace" then
        flags := flags ++ #[workspaceBind, toString (3 + inherited.size), ctx.workspace]
        inherited := inherited.push descriptors[0]!
      flags := flags ++ #["--chdir", ctx.workspace ++ "/" ++ String.intercalate "/" (parts args.cwd),
        "--json-status-fd", toString (3 + inherited.size), "--"] ++ args.argv
      body {args := flags, inherited := inherited.push statusWriter}

end Harness.Sandbox
