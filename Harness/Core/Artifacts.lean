import Harness.Core.State

/-!
Pure artifact registry checks. Validates artifact metadata (ID and hash format, label, byte counts,
truncation flag) and registers references from typed tool observations, including retained partial
output within per-artifact and session limits, rejecting changed identities. Authorizes `artifact`
reads only for registered IDs. Byte contents and hashes are verified by the IO adapter.
-/

namespace Harness

variable {app : Application}

def artifactHex (value : String) : Bool :=
  value.length == 64 && value.toList.all (fun c =>
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f'))

def artifactRefValid (config : Config) (ref : ArtifactRef) : Bool :=
  ref.id.startsWith "a-" && artifactHex (ref.id.drop 2 |>.toString) &&
  artifactHex ref.sha256 && ["output", "stdout", "stderr"].contains ref.label &&
  ref.storedBytes ≤ ref.totalBytes && ref.storedBytes ≤ config.maxArtifactBytes &&
  ref.truncated == (ref.storedBytes < ref.totalBytes)

def artifactBytes (refs : List ArtifactRef) : Nat :=
  (refs.map (·.storedBytes)).sum

/-- Only well-formed metadata from completed adapter observations grants retrieval
authority. A repeated ID must retain exactly the same immutable identity. -/
def registerArtifacts (config : Config) (existing : List ArtifactRef)
    (offered : Array ArtifactRef) : Except String (List ArtifactRef) := do
  if offered.size > 2 then throw "tool returned too many artifact references"
  offered.foldlM (init := existing) fun refs ref => do
    unless artifactRefValid config ref do throw "invalid artifact metadata"
    match refs.find? (fun item => item.id == ref.id) with
    | some prior =>
      if prior == ref then pure refs else throw "artifact identity changed"
    | none =>
      if refs.length ≥ 1024 || artifactBytes refs + ref.storedBytes > config.maxSessionArtifactBytes then
        throw "session artifact allowance exhausted"
      return refs ++ [ref]

def artifactAuthorized (s : State app) (call : Call app) : Bool :=
  match app.artifactRead call.operation with
  | some id => s.artifacts.any (fun ref => ref.id == id)
  | none => true

/-- Partial output can survive interruption without settling the tool call. Invalid
metadata gains no authority; the original observation remains in the journal. -/
def retainPartialArtifacts (s : State app) (result : Option ToolResult) : State app :=
  match result with
  | none => s
  | some result => match registerArtifacts s.config s.artifacts result.artifacts with
    | .ok artifacts => {s with artifacts}
    | .error _ => s

end Harness
