"""Explicit product checkout and local evaluation assets; importing performs no IO."""
import os
import re
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tomllib
from docker_endpoint import docker_host

EVAL_ROOT = Path(__file__).resolve().parents[1]
PRODUCT_SOURCE_PATHS = ["Harness.lean", "Harness", "runtime/native", "lakefile.lean", "lake-manifest.json",
                        "lean-toolchain", "rust-toolchain.toml"]


def product_source_hashes(root):
    names = subprocess.check_output(["git", "ls-files", "-c", "-o", "--exclude-standard", "-z", "--",
                                     *PRODUCT_SOURCE_PATHS], cwd=root).decode().split("\0")
    return {name: hashlib.sha256((Path(root) / name).read_bytes()).hexdigest()
            for name in sorted(set(names)) if name}


def add_harness_root_argument(parser):
    parser.add_argument("--harness-root", type=Path,
                        help="Product checkout containing .lake/build/bin/harness (or LEAN_HARNESS_ROOT)")


def harness_root(value=None):
    selected = value if value is not None else os.environ.get("LEAN_HARNESS_ROOT", EVAL_ROOT.parent)
    if not selected:
        raise RuntimeError("set LEAN_HARNESS_ROOT or pass --harness-root to an explicit lean-harness checkout")
    root = Path(selected).expanduser().resolve()
    if not (root / "Harness").is_dir() or not (root / "lean-toolchain").is_file():
        raise RuntimeError(f"invalid harness root: {root}; expected Harness/ and lean-toolchain")
    for name in ["lean-toolchain", "rust-toolchain.toml"]:
        local, product = EVAL_ROOT / name, root / name
        if local.is_file() and product.is_file() and local.read_bytes() != product.read_bytes():
            raise RuntimeError(f"{name} differs between evaluation workspace and harness root {root}")
    return root


def require_executable(path, label, advice):
    path = Path(path).expanduser().resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise RuntimeError(f"{label} missing or not executable: {path}; {advice}")
    return path


def harness_binary(root=None):
    return require_executable(harness_root(root) / ".lake/build/bin/harness", "harness binary",
                              "run lake build harness in the selected product checkout")


def require_fresh_harness(root=None):
    """Check Lake's existing build traces without compiling or fetching caches."""
    root = harness_root(root)
    binary = harness_binary(root)
    manifest = root / "lake-manifest.json"
    if not manifest.is_file():
        raise RuntimeError("product lake-manifest.json is missing; prepare dependencies explicitly before evaluation")
    try:
        data = json.loads(manifest.read_text())
        package_dir = root / data.get("packagesDir", ".lake/packages")
        for package in data.get("packages", []):
            dependency = (root / package["dir"] if package.get("type") == "path"
                          else package_dir / package["name"])
            if not dependency.is_dir():
                raise RuntimeError(f"missing cached product dependency {dependency}; prepare dependencies explicitly before evaluation")
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise RuntimeError(f"invalid product dependency manifest: {error}") from error
    lake = (command_path("lake", "LAKE_BIN") if os.environ.get("LAKE_BIN")
            else require_executable(lean_root() / "bin/lake", "Lake", "install the pinned Lean toolchain"))
    try:
        result = subprocess.run([str(lake), "--no-cache", "--no-build", "--rehash", "build", "harness"],
                                cwd=root, capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired as error:
        raise RuntimeError("product build freshness check timed out; verify the selected checkout offline") from error
    if result.returncode:
        raise RuntimeError("harness build is stale or could not be verified without rebuilding; "
                           "run lake build harness in the selected product checkout, then rebuild eval_tools_identity")
    return binary


def eval_tools_identity(root=None):
    root = harness_root(root)
    binary = require_executable(EVAL_ROOT / ".lake/build/bin/eval_tools", "evaluation tool proxy",
                                "build eval_tools_identity in the evaluation workspace")
    path = binary.with_name("eval_tools.identity.json")
    try:
        identity = json.loads(path.read_text())
        if identity["schema_version"] != 1 or Path(identity["harness_root"]).resolve() != root:
            raise ValueError("the proxy was built against a different product checkout")
        if hashlib.sha256(binary.read_bytes()).hexdigest() != identity["tool_binary_sha256"]:
            raise ValueError("the proxy binary changed after its build identity was recorded")
        if hashlib.sha256((EVAL_ROOT / "Tools.lean").read_bytes()).hexdigest() != identity["tool_source_sha256"]:
            raise ValueError("the proxy source changed after its build")
        sources = identity["harness_sources_sha256"]
        if not isinstance(sources, dict) or not sources:
            raise ValueError("the product source fingerprint is missing")
        for name, expected in sources.items():
            relative = Path(name)
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError("invalid product source path in proxy identity")
            if hashlib.sha256((root / relative).read_bytes()).hexdigest() != expected:
                raise ValueError(f"product source changed after proxy build: {name}")
        if sources != product_source_hashes(root):
            raise ValueError("product source inventory changed after proxy build")
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise RuntimeError(f"evaluation proxy identity missing, stale, or incompatible: {error}; "
                           "build eval_tools_identity against the selected --harness-root checkout") from error
    return identity


def eval_tools_binary(root=None):
    eval_tools_identity(root)
    return (EVAL_ROOT / ".lake/build/bin/eval_tools").resolve()


def command_path(name, variable=None, fallback=None):
    selected = os.environ.get(variable) if variable else None
    selected = selected or shutil.which(name)
    if not selected and fallback and Path(fallback).is_file():
        selected = fallback
    if not selected:
        raise RuntimeError(f"{name} unavailable; install it" + (f" or set {variable}" if variable else ""))
    return require_executable(selected, name, "install the pinned toolchain")


def require_compiler_version(binary, kind, expected):
    try:
        result = subprocess.run([str(binary), "--version"], cwd=EVAL_ROOT, capture_output=True,
                                text=True, timeout=10, check=True)
    except (subprocess.SubprocessError, OSError) as error:
        raise RuntimeError(f"cannot verify pinned {kind} compiler version") from error
    pattern = r"Lean \(version ([^, )]+)" if kind == "Lean" else r"rustc ([^ ]+)"
    match = re.search(pattern, result.stdout)
    if not match or match.group(1) != expected:
        raise RuntimeError(f"{kind} compiler does not match workspace pin {expected}")


def lean_root():
    """Use an installed compiler directly; an elan shim could download on use."""
    if os.environ.get("LEAN_BIN"):
        lean = command_path("lean", "LEAN_BIN")
    else:
        pin = (EVAL_ROOT / "lean-toolchain").read_text().strip()
        elan_home = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan")))
        installed = elan_home / "toolchains" / pin.replace("/", "--").replace(":", "---") / "bin/lean"
        lean = require_executable(installed, "pinned Lean compiler", "install the pinned toolchain explicitly or set LEAN_BIN")
    pin = (EVAL_ROOT / "lean-toolchain").read_text().strip()
    require_compiler_version(lean, "Lean", pin.rsplit(":v", 1)[-1])
    if not (lean.parent.parent / "lib/lean/Init.olean").is_file():
        raise RuntimeError("LEAN_BIN must name a concrete installed compiler, not an elan shim")
    try:
        prefix = subprocess.check_output([str(lean), "--print-prefix"], cwd=EVAL_ROOT,
                                         text=True, stderr=subprocess.PIPE).strip()
    except subprocess.CalledProcessError as error:
        raise RuntimeError("pinned Lean toolchain unavailable; install the version in lean-toolchain") from error
    root = Path(prefix).resolve()
    require_executable(root / "bin/lean", "Lean compiler", "install the pinned Lean toolchain")
    return root


def compiler_roots():
    """Resolve installed compilers using workspace pins, never the caller's cwd."""
    lean = lean_root()
    if os.environ.get("RUSTC_BIN"):
        rustc = command_path("rustc", "RUSTC_BIN")
    else:
        pin = EVAL_ROOT / "rust-toolchain.toml"
        if not pin.is_file():
            raise RuntimeError(f"missing evaluation Rust pin: {pin}")
        channel = tomllib.loads(pin.read_text())["toolchain"]["channel"]
        rustup = command_path("rustup", fallback=Path.home() / ".cargo/bin/rustup")
        try:
            rustc = subprocess.check_output([str(rustup), "which", "--toolchain", channel, "rustc"],
                                           cwd=EVAL_ROOT, text=True, stderr=subprocess.PIPE).strip()
        except subprocess.CalledProcessError as error:
            raise RuntimeError(f"pinned Rust toolchain {channel} unavailable; install it before evaluation") from error
        rustc = require_executable(rustc, "Rust compiler", "install the pinned Rust toolchain")
    channel = tomllib.loads((EVAL_ROOT / "rust-toolchain.toml").read_text())["toolchain"]["channel"]
    require_compiler_version(rustc, "Rust", channel)
    rust = Path(rustc).resolve().parent.parent
    if not (rust / "lib/rustlib").is_dir():
        raise RuntimeError("RUSTC_BIN must name a concrete installed compiler, not a rustup shim")
    return lean, rust


def node_identity(expected=None, binary=None):
    """Select a dedicated Node installation and bind the executable we will mount.

    PATH is convenient while preparing a draft. Paid coordinators supply the
    previously approved NODE_BIN explicitly; system prefixes cannot be mounted
    as a portable Node distribution.
    """
    executable = (require_executable(binary, "Node", "select a dedicated Node distribution")
                  if binary is not None else command_path("node", "NODE_BIN"))
    root = executable.parent.parent
    if executable != root / "bin/node" or root in map(Path, ["/", "/usr", "/usr/local", "/bin", "/sbin"]):
        raise RuntimeError("Node must be a dedicated distribution at ROOT/bin/node; set NODE_BIN explicitly")
    digest = hashlib.sha256(executable.read_bytes()).hexdigest()
    try:
        result = subprocess.run([str(executable), "--version"], capture_output=True, text=True,
                                timeout=10, check=True,
                                env={"PATH": os.defpath, "HOME": str(Path.home()), "LANG": "C.UTF-8"})
    except (OSError, subprocess.SubprocessError) as error:
        raise RuntimeError("cannot start the selected Node executable") from error
    version = result.stdout.strip()
    if not re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+", version):
        raise RuntimeError("Node returned an invalid version")
    if tuple(map(int, version[1:].split("."))) < (22, 19, 0):
        raise RuntimeError("pinned Pi 1.5.0 requires Node >=22.19.0")
    identity = {"schema_version": 1, "binary": str(executable), "root": str(root),
                "sha256": digest, "version": version}
    if expected is not None and identity != expected:
        raise RuntimeError("Node executable/root/hash/version differs from the frozen identity")
    return identity


def node_root():
    return Path(node_identity()["root"])


def validate_node_preflight(output, identity, model):
    """Check the no-prompt Pi startup marker from the actual candidate image."""
    if len(output.encode()) > 4096:
        raise RuntimeError("Pi startup preflight output exceeded its allowance")
    try:
        observed = json.loads(output)
    except (ValueError, TypeError) as error:
        raise RuntimeError("Pi startup preflight did not return its completion marker") from error
    expected = {"status": "ok", "nodeVersion": identity["version"],
                "nodeSha256": identity["sha256"], "model": model,
                "piVersion": "1.5.0", "providerRequests": 0}
    if observed != expected:
        raise RuntimeError("Pi startup preflight identity/completion marker mismatch")
    return observed


def evaluation_provenance():
    names = subprocess.check_output(["git", "ls-files", "-c", "-o", "--exclude-standard", "-z", "--",
        "runner", "baseline/run.mjs", "baseline/preflight.mjs", "baseline/context-settings.mjs",
        "Tools.lean", "corpus/check.py", "corpus/validate.py",
        "lakefile.lean", "lake-manifest.json", "lean-toolchain", "rust-toolchain.toml"], cwd=EVAL_ROOT).decode().split("\0")
    return {"evaluation_root": str(EVAL_ROOT), "docker_endpoint": docker_host(),
            "evaluation_sources_sha256": {name: hashlib.sha256((EVAL_ROOT / name).read_bytes()).hexdigest()
                                           for name in sorted(set(names)) if name},
            "evaluation_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=EVAL_ROOT,
                                                          text=True).strip(),
            "evaluation_dirty_source_tree": bool(subprocess.check_output(
                ["git", "status", "--porcelain", "--", "."], cwd=EVAL_ROOT, text=True))}


def product_provenance(root=None):
    root = harness_root(root)
    return {"harness_root": str(root),
            "harness_sources_sha256": product_source_hashes(root),
            "harness_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root,
                                                       text=True).strip(),
            "dirty_source_tree": bool(subprocess.check_output(
                ["git", "status", "--porcelain"], cwd=root, text=True))}
