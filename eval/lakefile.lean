import Lake
open Lake DSL Lean System

package lean_harness_evals where
  version := v!"0.1.0"
  -- Dependency archives are linked transitively; package link flags are not.
  moreLinkArgs := #["-lcrypto"]

-- This evaluation package is part of the same repository, but is not a product
-- build target. Its dependency is the enclosing product package.
require lean_harness from ".."

lean_exe eval_tools where
  root := `Tools

private def checkedOutput (cmd : String) (args : Array String)
    (cwd : Option FilePath := none) : IO String := do
  let result ← IO.Process.output { cmd, args, cwd }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"{cmd} failed while recording tool-proxy provenance: {result.stderr}"
  return result.stdout

private def fileHash (path : FilePath) : IO String := do
  let output ← checkedOutput "sha256sum" #["--", path.toString]
  return output.take 64 |>.toString

/-- Bind the proxy to the actual dependency loaded by Lake, including local overrides.
This is provenance under the trusted build environment, not binary attestation.
Runners must reject missing/stale metadata rather than assume a sibling checkout. -/
@[default_target]
target eval_tools_identity pkg : FilePath := do
  let some product ← findPackageByName? `lean_harness
    | error "lean_harness dependency is unavailable"
  let some executable := pkg.findLeanExe? `eval_tools
    | error "eval_tools executable is unavailable"
  let binary ← executable.exe.fetch
  binary.mapM fun path => do
    let productRoot ← IO.FS.realPath product.dir
    let revision ← checkedOutput "git" #["rev-parse", "HEAD"] (some productRoot)
    let files ← checkedOutput "git" #["ls-files", "-c", "-o", "--exclude-standard", "-z", "--",
      "Harness", "Harness.lean", "runtime/native", "lakefile.lean", "lake-manifest.json",
      "lean-toolchain", "rust-toolchain.toml"] (some productRoot)
    let names := (files.splitOn "\u0000").filter (!·.isEmpty) |>.mergeSort (· ≤ ·)
    let hashes ← names.mapM fun (name : String) => do
      return (name, toJson (← fileHash (productRoot / FilePath.mk name)))
    let identity := Json.mkObj [
      ("schema_version", toJson (1 : Nat)),
      ("harness_root", toJson productRoot.toString),
      ("harness_commit", toJson revision.trimAscii.toString),
      ("harness_sources_sha256", Json.mkObj hashes),
      ("tool_binary_sha256", toJson (← fileHash path)),
      ("tool_source_sha256", toJson (← fileHash (pkg.dir / "Tools.lean")))]
    let destination := pkg.buildDir / "bin" / "eval_tools.identity.json"
    let temporary := destination.withExtension "json.tmp"
    IO.FS.writeFile temporary (identity.compress ++ "\n")
    IO.FS.rename temporary destination
    return destination
