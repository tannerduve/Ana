import Lake
open Lake DSL

package lean_harness where
  version := v!"0.1.0"
  moreLinkArgs := #["-lcrypto"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

extern_lib harness_native pkg := do
  let native := pkg.dir / "runtime" / "native"
  let sources ← inputDir (native / "src") true (fun path => path.extension == some "rs")
  let includeDir ← getLeanIncludeDir
  let metadata ← #[native / "Cargo.toml", native / "Cargo.lock", native / "build.rs",
    pkg.dir / "rust-toolchain.toml", pkg.dir / "lean-toolchain",
    includeDir / "lean" / "lean.h", includeDir / "lean" / "config.h",
    includeDir / "lean" / "version.h"].mapM fun path => do
      inputTextFile path
  let dependencies := Job.zipWith (fun _ _ => ()) sources (Job.collectArray metadata)
  let targetDir := pkg.buildDir / "rust-native"
  let library := targetDir / "release" / nameToStaticLib "harness_native"
  buildFileAfterDep library dependencies fun _ => do
    proc {
      cmd := "cargo"
      args := #["build", "--locked", "--release", "--manifest-path", (native / "Cargo.toml").toString,
        "--target-dir", targetDir.toString]
      env := #[("LEAN_INCLUDE_DIR", some includeDir.toString)] }

@[default_target] lean_lib Harness
lean_lib Tests

lean_exe eval_tools where
  root := `eval.Tools

@[default_target] lean_exe harness where
  root := `Harness.CLI

@[default_target] lean_exe harness_tests where
  root := `Tests.Main

@[default_target] lean_exe runtime_contracts where
  root := `Tests.Runtime

@[default_target] lean_exe runtime_properties where
  root := `Tests.RuntimeProperties
