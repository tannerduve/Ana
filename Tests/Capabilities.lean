import Plausible.Testable
import Harness.Core.Capabilities

/-!
Executable policy-format and scope regressions. Positive containment fixtures
prevent a vacuous always-rejecting checker from satisfying the test suite.
Generated paths exercise aliases and sibling-prefix collisions; generated codecs
preserve literal arguments and resource identities without invoking real tools.
-/
namespace Tests.Capabilities
open Lean Harness.Capability Plausible

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"capabilities: {label}"

private def parseAccess (text : String) : Except String Access := do
  fromJson? (← Json.parse text)

private def pathContract (sample : Nat × Nat) : Bool :=
  let root := s!"dir{sample.1}"
  let file := s!"file{sample.2}"
  let rule : Access := .read (.tree root)
  covers rule (.read (.exact s!"{root}/{file}")) &&
    covers rule (.read (.tree s!"./{root}//./child")) &&
    !covers rule (.read (.exact s!"{root}-private/{file}")) &&
    !covers rule (.read (.exact s!"{root}/../{file}")) &&
    !covers rule (.read (.exact s!"/{root}/{file}")) &&
    !covers (.read (.exact root)) (.read (.tree root)) &&
    !covers rule (.write (.exact s!"{root}/{file}"))

private def codecContract (sample : Nat × Nat) : Bool :=
  let resource := s!"sku-{sample.1}-λ"
  let literal := s!"argument {sample.2} '\" $() ; λ🙂"
  let accesses : List Access := [
    .read (.exact s!"src/file{sample.1}"), .write (.tree "."),
    .process #["tool", "", literal] "./src//.", .processes,
    .artifact s!"artifact-{sample.1}", .artifacts,
    .resource "inventory" "lookup" (.exact resource),
    .resource "inventory" "warehouse_totals" .all, .everything]
  accesses.all fun access =>
    match Json.parse (toJson access).compress with
    | .error _ => false
    | .ok json => (fromJson? json : Except String Access).toOption == some access

private def generated (label : String) (property : Prop) [Testable property]
    (seed : Nat) : IO Unit := do
  match ← Testable.checkIO property {numInst := 300, maxSize := 32, randomSeed := some seed} with
  | .success _ => pure ()
  | .gaveUp count => throw <| IO.userError s!"{label}: gave up after {count} samples"
  | .failure _ examples shrinks =>
    throw <| IO.userError s!"{label}: seed {seed}, shrinks {shrinks}, {examples}"

def run : IO Unit := do
  let parent : Policy := [[.read (.tree "."), .write (.tree "drafts")]]
  let limit : List Access := [.read (.tree "docs"), .write (.exact "drafts/result.md")]
  let child := restrict parent limit
  check "restrict must retain parent ceilings" (child == parent ++ [limit])
  check "contained restriction accepted" (checkContained child parent)
  check "same valid policy accepted" (checkContained parent parent)
  check "deny-all child accepted" (checkContained [[]] parent)
  check "unrestricted parent accepted" (checkContained parent [])
  check "broader parent not certified as child" (!checkContained parent child)
  check "empty declaration cannot bypass ceilings" (!permitsAll [] [])
  check "empty ceiling denies" (!permits [[]] (.read (.exact "docs/a")))
  check "restriction admits required read" (permits child (.read (.exact "docs/a")))
  check "restriction denies other read" (!permits child (.read (.exact "src/a")))
  check "restriction admits exact output" (permits child (.write (.exact "drafts/result.md")))
  check "restriction denies sibling output" (!permits child (.write (.exact "drafts/other.md")))
  check "parent cannot be bypassed by later everything" <|
    !permits (restrict parent [.everything]) (.write (.exact "src/a"))
  let command : Access := .process #["pytest", "-q"] "tests"
  check "command matches normalized directory" (covers command (.process #["pytest", "-q"] "./tests//."))
  check "extra argument changes invocation" (!covers command (.process #["pytest", "-q", "--extra"] "tests"))
  check "argument order matters" (!covers command (.process #["-q", "pytest"] "tests"))
  check "working directory matters" (!covers command (.process #["pytest", "-q"] "."))
  check "resources are application-namespaced" <|
    !covers (.resource "inventory" "lookup" .all) (.resource "other" "lookup" (.exact "A"))
  check "resource read does not grant mutation" <|
    !covers (.resource "inventory" "lookup" .all) (.resource "inventory" "reserve" (.exact "A"))
  for invalid in [
      "{}", "null", "{\"kind\":\"unknown\"}",
      "{\"kind\":\"everything\",\"extra\":true}",
      "{\"kind\":\"read\",\"scope\":{\"kind\":\"tree\",\"path\":\"docs\",\"extra\":true}}",
      "{\"kind\":\"read\",\"scope\":{\"kind\":\"tree\",\"path\":\"../docs\"}}",
      "{\"kind\":\"process\",\"argv\":[],\"cwd\":\".\"}",
      "{\"kind\":\"process\",\"argv\":[\"\"],\"cwd\":\".\"}",
      "{\"kind\":\"artifact\",\"id\":\"\"}",
      "{\"kind\":\"resource\",\"application\":\"inventory\",\"action\":\"lookup\",\"scope\":{\"kind\":\"all\",\"value\":\"ignored\"}}"] do
    check "malformed or ambiguous capability rejected" (parseAccess invalid).toOption.isNone
  check "policy layer bound" (validate (List.replicate (maxLayers + 1) [])).toOption.isNone
  check "policy grant bound" (validate [List.replicate (maxGrants + 1) .everything]).toOption.isNone
  check "valid policy accepted" (validate child).toOption.isSome
  generated "normalized component scopes"
    (NamedBinder "sample" (∀ sample : Nat × Nat, pathContract sample = true)) 53001
  generated "strict capability wire roundtrips"
    (NamedBinder "sample" (∀ sample : Nat × Nat, codecContract sample = true)) 53002
  IO.println "Capability format/scope fixtures and 600 Plausible-generated cases passed."

end Tests.Capabilities
