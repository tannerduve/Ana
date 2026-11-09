//! Refuse to compile hand-mirrored runtime layouts against unreviewed headers.
//! The FNV-1a fingerprints detect changes; they are not authentication.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn fingerprint(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf29ce484222325_u64, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
    })
}

fn checked_header(include: &Path, name: &str, expected: u64) {
    let path = include.join("lean").join(name);
    println!("cargo:rerun-if-changed={}", path.display());
    let bytes = fs::read(&path)
        .unwrap_or_else(|error| panic!("cannot read Lean ABI header {}: {error}", path.display()));
    assert_eq!(
        fingerprint(&bytes),
        expected,
        "unreviewed Lean runtime header {}; review lean.rs before updating this fingerprint",
        path.display()
    );
    if name == "config.h" {
        assert!(
            String::from_utf8_lossy(&bytes)
                .lines()
                .any(|line| line == "#define LEAN_MIMALLOC"),
            "Lean ABI bindings require the pinned mimalloc runtime"
        );
    }
}

fn main() {
    println!("cargo:rerun-if-env-changed=LEAN_INCLUDE_DIR");
    assert_eq!(
        env::var("TARGET").expect("Cargo TARGET"),
        "x86_64-unknown-linux-gnu",
        "the native Lean ABI has only been reviewed for x86_64 Linux/glibc"
    );
    let manifest =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("Cargo manifest directory"));
    let root = manifest
        .parent()
        .and_then(Path::parent)
        .expect("runtime/native inside repository");
    let toolchain = root.join("lean-toolchain");
    println!("cargo:rerun-if-changed={}", toolchain.display());
    assert_eq!(
        fs::read_to_string(&toolchain)
            .expect("read lean-toolchain")
            .trim(),
        "leanprover/lean4:v4.33.1",
        "Lean version changed: review native ABI bindings before updating this guard"
    );
    let include = env::var_os("LEAN_INCLUDE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            let output = Command::new("lean")
                .arg("--print-prefix")
                .current_dir(root)
                .output()
                .expect("set LEAN_INCLUDE_DIR or put the pinned lean executable on PATH");
            assert!(
                output.status.success(),
                "lean --print-prefix failed; set LEAN_INCLUDE_DIR"
            );
            let prefix = String::from_utf8(output.stdout).expect("Lean prefix must be UTF-8");
            PathBuf::from(prefix.trim()).join("include")
        });
    checked_header(&include, "lean.h", 0x6ac85ad391a18ab6);
    checked_header(&include, "config.h", 0x80656324644ff183);
    checked_header(&include, "version.h", 0xf9e0d4d67ca35346);

    // Only lean.rs's cfg(test) extern block requests this dynamic library.
    // The search path and rpath let `cargo test` link and run without ambient
    // LD_LIBRARY_PATH. Production emits a static archive; Lake resolves its
    // runtime symbols, so this adds no production dynamic-link dependency.
    let runtime = include
        .parent()
        .expect("Lean include directory inside toolchain prefix")
        .join("lib/lean");
    println!("cargo:rustc-link-search=native={}", runtime.display());
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", runtime.display());
}
