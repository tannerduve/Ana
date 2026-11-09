import Lean

/-!
Finite capability ceilings. Each policy layer is a union of grants; every layer
must cover every requested access. Adding a layer therefore restricts authority.
Paths denote lexical workspace-relative scopes, not filesystem resolution.
Process grants authorize an exact invocation, not all effects of that process.
The application supplies the complete demand list; an empty list is refused.
-/
namespace Harness.Capability
open Lean

def maxLayers : Nat := 32
def maxGrants : Nat := 1024
def maxPathChars : Nat := 4096
def maxPathComponents : Nat := 256
def maxArgc : Nat := 256
def maxArgumentChars : Nat := 4096
def maxArgvChars : Nat := 65536
def maxIdentityChars : Nat := 256
def maxArtifactIdChars : Nat := 80

inductive PathScope where
  | exact (path : String)
  | tree (path : String)
  deriving Repr, BEq, DecidableEq

inductive ResourceScope where
  | exact (value : String)
  | all
  deriving Repr, BEq, DecidableEq

inductive Access where
  | read (scope : PathScope)
  | write (scope : PathScope)
  | process (argv : Array String) (cwd : String)
  | processes
  | artifact (id : String)
  | artifacts
  | resource (application : String) (action : String) (scope : ResourceScope)
  | everything
  deriving Repr, BEq, DecidableEq

/-- An empty policy is unrestricted; a policy containing an empty layer denies all. -/
abbrev Policy := List (List Access)

/-- Reject traversal before removing harmless aliases. `.` denotes the root. -/
def normalizePath (path : String) : Option (List String) :=
  let parts := path.splitOn "/"
  if path.isEmpty || path.startsWith "/" || path.toList.contains '\x00' || parts.contains ".." then
    none
  else some (parts.filter (fun part => !part.isEmpty && part != "."))

def PathScope.path : PathScope → String
  | .exact path | .tree path => path

def PathScope.covers (grant demand : PathScope) : Bool :=
  match normalizePath grant.path, normalizePath demand.path with
  | some parent, some child =>
    match grant, demand with
    | .exact _, .exact _ => decide (parent = child)
    | .tree _, _ => decide (parent <+: child)
    | _, _ => false
  | _, _ => false

def ResourceScope.covers (grant demand : ResourceScope) : Bool :=
  match grant, demand with
  | .all, _ => true
  | .exact parent, .exact child => parent == child
  | _, _ => false

/-- Grant coverage includes scope-to-scope coverage for the containment checker. -/
def covers (grant demand : Access) : Bool :=
  match grant, demand with
  | .everything, _ => true
  | .read parent, .read child | .write parent, .write child => parent.covers child
  | .process argv cwd, .process otherArgv otherCwd =>
    argv == otherArgv && match normalizePath cwd, normalizePath otherCwd with
      | some parent, some child => decide (parent = child)
      | _, _ => false
  | .processes, .process _ _ | .processes, .processes => true
  | .artifact id, .artifact other => id == other
  | .artifacts, .artifact _ | .artifacts, .artifacts => true
  | .resource app action parent, .resource otherApp otherAction child =>
    app == otherApp && action == otherAction && parent.covers child
  | _, _ => false

def permits (policy : Policy) (demand : Access) : Bool :=
  policy.all (fun layer => layer.any (fun grant => covers grant demand))

/-- An application cannot bypass a ceiling by reporting no required accesses. -/
def permitsAll (policy : Policy) (demands : List Access) : Bool :=
  !demands.isEmpty && demands.all (permits policy)

def intersect (left right : Policy) : Policy := left ++ right
def restrict (parent : Policy) (layer : List Access) : Policy := parent ++ [layer]

def Contained (child parent : Policy) : Prop :=
  ∀ demand, permits child demand = true → permits parent demand = true

/-- Sufficient finite coverage, not a complete decision procedure for semantic
containment. False means containment was not established; it is not a witness. -/
def checkContained (child parent : Policy) : Bool :=
  parent.all (fun upper => child.any (fun lower =>
    lower.all (fun grant => upper.any (fun ceiling => covers ceiling grant))))

private def noNul (value : String) : Bool := !value.toList.contains '\x00'

def validIdentity (value : String) (limit : Nat := maxIdentityChars) : Bool :=
  !value.isEmpty && value.length ≤ limit && noNul value

def validPath (path : String) : Bool :=
  path.length ≤ maxPathChars && match normalizePath path with
    | none => false
    | some components => components.length ≤ maxPathComponents

def validArgv (argv : Array String) : Bool :=
  !argv.isEmpty && argv.size ≤ maxArgc &&
    !(argv[0]?.getD "").isEmpty &&
    argv.all (fun arg => arg.length ≤ maxArgumentChars && noNul arg) &&
    (argv.foldl (fun total arg => total + arg.length) 0) ≤ maxArgvChars

def validateAccess : Access → Except String Unit
  | .read scope | .write scope => do
    unless validPath scope.path do throw "invalid capability path scope"
  | .process argv cwd => do
    unless validArgv argv && validPath cwd do throw "invalid capability process invocation"
  | .artifact id => do
    unless validIdentity id maxArtifactIdChars do throw "invalid capability artifact identity"
  | .resource application action scope => do
    unless validIdentity application && validIdentity action do
      throw "invalid capability application/action identity"
    match scope with
    | .all => pure ()
    | .exact value => unless validIdentity value do throw "invalid capability resource identity"
  | .processes | .artifacts | .everything => pure ()

def validate (policy : Policy) : Except String Unit := do
  unless policy.length ≤ maxLayers do throw "too many capability policy layers"
  unless (policy.foldl (fun count layer => count + layer.length) 0) ≤ maxGrants do
    throw "too many capability grants"
  for layer in policy do
    for grant in layer do validateAccess grant

private def exactFields (json : Json) (names : List String) : Except String Unit := do
  let fields ← json.getObj?
  unless fields.size == names.length && fields.toList.all (fun pair => names.contains pair.1) do
    throw "unexpected or missing capability fields"

def PathScope.toJson : PathScope → Json
  | .exact path => Json.mkObj [("kind", Lean.toJson "exact"), ("path", Lean.toJson path)]
  | .tree path => Json.mkObj [("kind", Lean.toJson "tree"), ("path", Lean.toJson path)]

instance : ToJson PathScope := ⟨PathScope.toJson⟩

def PathScope.fromJson (json : Json) : Except String PathScope := do
  exactFields json ["kind", "path"]
  let kind ← json.getObjValAs? String "kind"
  let path ← json.getObjValAs? String "path"
  unless validPath path do throw "invalid capability path scope"
  match kind with
  | "exact" => pure (.exact path)
  | "tree" => pure (.tree path)
  | _ => throw "unknown capability path scope"

instance : FromJson PathScope := ⟨PathScope.fromJson⟩

def ResourceScope.toJson : ResourceScope → Json
  | .exact value => Json.mkObj [("kind", Lean.toJson "exact"), ("value", Lean.toJson value)]
  | .all => Json.mkObj [("kind", Lean.toJson "all")]

instance : ToJson ResourceScope := ⟨ResourceScope.toJson⟩

def ResourceScope.fromJson (json : Json) : Except String ResourceScope := do
  let kind ← json.getObjValAs? String "kind"
  match kind with
  | "exact" =>
    exactFields json ["kind", "value"]
    let value ← json.getObjValAs? String "value"
    unless validIdentity value do throw "invalid capability resource identity"
    pure (.exact value)
  | "all" => exactFields json ["kind"]; pure .all
  | _ => throw "unknown capability resource scope"

instance : FromJson ResourceScope := ⟨ResourceScope.fromJson⟩

def Access.toJson : Access → Json
  | .read scope => Json.mkObj [("kind", Lean.toJson "read"), ("scope", Lean.toJson scope)]
  | .write scope => Json.mkObj [("kind", Lean.toJson "write"), ("scope", Lean.toJson scope)]
  | .process argv cwd => Json.mkObj [("kind", Lean.toJson "process"), ("argv", Lean.toJson argv), ("cwd", Lean.toJson cwd)]
  | .processes => Json.mkObj [("kind", Lean.toJson "processes")]
  | .artifact id => Json.mkObj [("kind", Lean.toJson "artifact"), ("id", Lean.toJson id)]
  | .artifacts => Json.mkObj [("kind", Lean.toJson "artifacts")]
  | .resource application action scope => Json.mkObj [("kind", Lean.toJson "resource"),
      ("application", Lean.toJson application), ("action", Lean.toJson action), ("scope", Lean.toJson scope)]
  | .everything => Json.mkObj [("kind", Lean.toJson "everything")]

instance : ToJson Access := ⟨Access.toJson⟩

def Access.fromJson (json : Json) : Except String Access := do
  let kind ← json.getObjValAs? String "kind"
  let access ← match kind with
    | "read" => exactFields json ["kind", "scope"]; Access.read <$> json.getObjValAs? PathScope "scope"
    | "write" => exactFields json ["kind", "scope"]; Access.write <$> json.getObjValAs? PathScope "scope"
    | "process" => do
      exactFields json ["kind", "argv", "cwd"]
      pure (.process (← json.getObjValAs? (Array String) "argv") (← json.getObjValAs? String "cwd"))
    | "processes" => exactFields json ["kind"]; pure .processes
    | "artifact" => exactFields json ["kind", "id"]; Access.artifact <$> json.getObjValAs? String "id"
    | "artifacts" => exactFields json ["kind"]; pure .artifacts
    | "resource" => do
      exactFields json ["kind", "application", "action", "scope"]
      pure (.resource (← json.getObjValAs? String "application")
        (← json.getObjValAs? String "action") (← json.getObjValAs? ResourceScope "scope"))
    | "everything" => exactFields json ["kind"]; pure .everything
    | _ => throw "unknown capability access kind"
  validateAccess access
  pure access

instance : FromJson Access := ⟨Access.fromJson⟩

end Harness.Capability
