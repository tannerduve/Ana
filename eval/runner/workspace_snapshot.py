"""Trusted byte snapshots for candidate extraction; never execute candidate Git.

Docker supplies an archive of a stopped workspace. We read bounded regular-file
and symlink bytes without extracting filesystem paths, then build two trees in a
fresh host-owned bare repository. Hooks, filters, text conversion, candidate Git
configuration and candidate executables are outside this extraction path.
"""
from contextlib import contextmanager
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import subprocess
import tarfile
import threading
from docker_endpoint import command_environment


LIMITS = {"archive_bytes": 512 * 1024 * 1024, "file_bytes": 64 * 1024 * 1024,
          "entries": 200000, "path_bytes": 4096, "patch_bytes": 64 * 1024 * 1024,
          "seconds": 120}
CACHE_DIRECTORIES = frozenset({"__pycache__", ".pytest_cache", ".mypy_cache",
                               ".ruff_cache", ".hypothesis"})
EXCLUSION_POLICY = "Only new __pycache__/.pytest_cache/.mypy_cache/.ruff_cache/.hypothesis entries and new .pyc/.pyo files; every baseline path remains authoritative. Top-level .git metadata is excluded."
SESSION_LIMITS = {"entries": 8192, "depth": 128, "file_bytes": 64 * 1024 * 1024,
                  "total_bytes": 256 * 1024 * 1024, "path_bytes": 4096}


class SnapshotError(RuntimeError):
    pass


def _environment(store):
    # Construct from scratch: no GIT_CONFIG_COUNT, GIT_EXTERNAL_DIFF, templates,
    # inherited Git directories, global attributes, hooks or credential helpers.
    return {"PATH": "/usr/bin:/bin", "HOME": str(store), "LC_ALL": "C.UTF-8",
            "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null",
            "GIT_ATTR_NOSYSTEM": "1", "GIT_CONFIG_SYSTEM": "/dev/null",
            "GIT_OPTIONAL_LOCKS": "0"}


def _git(store, *arguments, data=None):
    command = ["/usr/bin/git", "--git-dir=" + str(store), "-c", "core.hooksPath=/dev/null",
               "-c", "core.attributesFile=/dev/null", *arguments]
    result = subprocess.run(command, input=data, capture_output=True, env=_environment(store),
                            cwd=store.parent, timeout=LIMITS["seconds"])
    if result.returncode:
        raise SnapshotError("trusted Git operation failed: " + arguments[0])
    return result.stdout


def _new_store(output):
    output = Path(output)
    output.mkdir(mode=0o700, parents=True, exist_ok=False)
    store = output / "objects.git"
    subprocess.run(["/usr/bin/git", "-c", "core.hooksPath=/dev/null", "init", "--bare",
                    "--template=", "--quiet", str(store)], check=True, env=_environment(output),
                   cwd=output, capture_output=True, timeout=LIMITS["seconds"])
    return store


class _BoundedReader:
    def __init__(self, source):
        self.source, self.total = source, 0

    def read(self, size=-1):
        remaining = LIMITS["archive_bytes"] - self.total
        data = self.source.read(min(size if size >= 0 else remaining + 1, remaining + 1))
        self.total += len(data)
        if self.total > LIMITS["archive_bytes"]:
            raise SnapshotError("workspace archive byte limit exceeded")
        return data


def _path(name):
    if "\x00" in name or name.startswith("/"):
        raise SnapshotError("unsafe archive path")
    components = name.split("/")
    if ".." in components:
        raise SnapshotError("archive path escapes workspace")
    value = "/".join(part for part in components if part not in {"", "."})
    try:
        encoded = value.encode("utf-8", "strict")
    except UnicodeError as error:
        raise SnapshotError("archive path is not UTF-8") from error
    if len(encoded) > LIMITS["path_bytes"]:
        raise SnapshotError("archive path length limit exceeded")
    return value


def _new_cache(path):
    parts = PurePosixPath(path).parts
    return any(part in CACHE_DIRECTORIES for part in parts) or path.endswith((".pyc", ".pyo"))


def _read_snapshot(source, store):
    reader = _BoundedReader(source)
    manifest, kinds, count, bytes_read = {}, {}, 0, 0
    with tarfile.open(fileobj=reader, mode="r|*") as archive:
        for member in archive:
            count += 1
            if count > LIMITS["entries"]:
                raise SnapshotError("workspace entry limit exceeded")
            name = _path(member.name)
            if not name:
                if not member.isdir():
                    raise SnapshotError("workspace root is not a directory")
                continue
            if name == ".git" or name.startswith(".git/"):
                continue
            if name in kinds:
                raise SnapshotError("duplicate archive path")
            kinds[name] = "directory" if member.isdir() else "entry"
            if member.isdir():
                continue
            if member.isreg():
                if member.size > LIMITS["file_bytes"]:
                    raise SnapshotError("workspace file byte limit exceeded")
                stream = archive.extractfile(member)
                if stream is None:
                    raise SnapshotError("archive file has no data")
                data = stream.read(LIMITS["file_bytes"] + 1)
                if len(data) != member.size:
                    raise SnapshotError("workspace file was truncated")
                mode = "100755" if member.mode & 0o111 else "100644"
                kind = "file"
            elif member.issym():
                try:
                    data = member.linkname.encode("utf-8", "strict")
                except UnicodeError as error:
                    raise SnapshotError("symlink target is not UTF-8") from error
                if len(data) > LIMITS["path_bytes"] or b"\x00" in data:
                    raise SnapshotError("symlink target exceeds supported bounds")
                mode, kind = "120000", "symlink"
            else:
                # Never follow archive hard links, devices, FIFOs or sockets.
                raise SnapshotError("unsupported workspace entry type: " + name)
            bytes_read += len(data)
            if bytes_read > LIMITS["archive_bytes"]:
                raise SnapshotError("workspace content byte limit exceeded")
            blob = _git(store, "hash-object", "-w", "--stdin", "--no-filters", data=data).decode().strip()
            manifest[name] = {"kind": kind, "mode": mode, "bytes": len(data),
                              "sha256": hashlib.sha256(data).hexdigest(), "blob": blob}
    # An entry under a symlink/file is invalid even if the archive orders the
    # child first. No filesystem extraction occurred before this check.
    for name in kinds:
        for parent in PurePosixPath(name).parents:
            if str(parent) != "." and kinds.get(str(parent)) == "entry":
                raise SnapshotError("archive entry has a non-directory ancestor")
    return manifest, {"archive_entries": count, "content_bytes": bytes_read,
                      "archive_bytes_read": reader.total}


@contextmanager
def _docker_stream(container, source, timeout_seconds=None):
    if not source.startswith("/") or "\x00" in source:
        raise SnapshotError("source must be an absolute container path")
    timeout = LIMITS["seconds"] if timeout_seconds is None else float(timeout_seconds)
    if not math.isfinite(timeout) or timeout <= 0:
        raise SnapshotError("archive deadline must be positive and finite")
    process = subprocess.Popen(["/usr/bin/docker", "cp", container + ":" + source, "-"],
                               stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                               env=command_environment())
    timer = threading.Timer(min(timeout, LIMITS["seconds"]), process.kill)
    timer.daemon = True
    timer.start()
    try:
        yield process.stdout
        # tarfile stops at its EOF marker; drain bounded padding so Docker can
        # finish. A normal Docker archive contains only short trailing padding.
        remainder = process.stdout.read(1024 * 1024 + 1)
        if len(remainder) > 1024 * 1024:
            raise SnapshotError("unexpected archive trailing data")
        if process.wait(timeout=5):
            raise SnapshotError("Docker workspace archive failed or timed out")
    finally:
        timer.cancel()
        if process.poll() is None:
            process.kill()
        process.wait(timeout=5)
        process.stdout.close()


def _docker_archive(container, workspace):
    return _docker_stream(container, workspace.rstrip("/") + "/.")


def read_regular_file(container, absolute_path, max_bytes, *, timeout_seconds=None):
    """Read one small grader result without following archive links or extracting."""
    if type(max_bytes) is not int or not 0 < max_bytes <= LIMITS["file_bytes"]:
        raise SnapshotError("invalid grader result byte limit")
    found = None
    with _docker_stream(container, absolute_path, timeout_seconds) as source:
        with tarfile.open(fileobj=_BoundedReader(source), mode="r|*") as archive:
            for member in archive:
                name = _path(member.name)
                if found is not None or not name or not member.isreg() or not 0 <= member.size <= max_bytes:
                    raise SnapshotError("grader result is not one bounded regular file")
                stream = archive.extractfile(member)
                if stream is None:
                    raise SnapshotError("grader result has no data")
                found = stream.read(max_bytes + 1)
                if len(found) != member.size:
                    raise SnapshotError("grader result was truncated")
    if found is None:
        raise SnapshotError("grader result is missing")
    return found


def _export_regular_tree(source, destination):
    """Export to a fresh trusted directory; no archive extraction API is used."""
    destination = Path(destination)
    destination.mkdir(mode=0o700, parents=True, exist_ok=False)
    files, seen, total = {}, set(), 0
    with tarfile.open(fileobj=_BoundedReader(source), mode="r|") as archive:
        for member in archive:
            name = _path(member.name)
            if name in seen:
                raise SnapshotError("duplicate session archive path")
            seen.add(name)
            if len(seen) > SESSION_LIMITS["entries"]:
                raise SnapshotError("session entry limit exceeded")
            if len(PurePosixPath(name).parts) > SESSION_LIMITS["depth"]:
                raise SnapshotError("session path depth exceeded")
            if not name:
                if not member.isdir():
                    raise SnapshotError("session root is not a directory")
                continue
            path = destination / name
            if member.isdir():
                path.mkdir(mode=0o700, parents=True, exist_ok=True)
                continue
            if not member.isreg():
                raise SnapshotError("session contains a link or special file")
            if not 0 <= member.size <= SESSION_LIMITS["file_bytes"]:
                raise SnapshotError("session file byte limit exceeded")
            total += member.size
            if total > SESSION_LIMITS["total_bytes"]:
                raise SnapshotError("session total byte limit exceeded")
            stream = archive.extractfile(member)
            if stream is None:
                raise SnapshotError("session file has no data")
            path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
            digest = hashlib.sha256()
            received = 0
            # All parents were created here; archive symlinks and hard links are
            # rejected. O_EXCL additionally prevents replacing a prior entry.
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
            with os.fdopen(fd, "wb") as target:
                while chunk := stream.read(65536):
                    received += len(chunk)
                    if received > member.size:
                        raise SnapshotError("session file exceeds declared length")
                    target.write(chunk)
                    digest.update(chunk)
            if received != member.size:
                raise SnapshotError("session archive file was truncated")
            files[name] = {"bytes": received, "sha256": digest.hexdigest()}
    return {"files": files, "entries": len(seen), "total_bytes": total, "limits": SESSION_LIMITS,
            "provenance": "host-owned regular-file audit mirror copied by trusted Docker archive reader after candidate stop; original container session was not modified"}


def mirror_session_after_stop(container, source_dir, destination):
    """Create a bounded fresh audit mirror, retaining original storage in Docker."""
    _require_stopped(container)
    with _docker_archive(container, source_dir) as source:
        result = _export_regular_tree(source, destination)
    result.update(source_container=container, source_path=source_dir, mirror_path=str(destination))
    return result


def _tree(store, manifest):
    _git(store, "read-tree", "--empty")
    index = b"".join((row["mode"] + " " + row["blob"] + "\t" + name).encode() + b"\0"
                     for name, row in sorted(manifest.items()))
    _git(store, "update-index", "-z", "--index-info", data=index)
    return _git(store, "write-tree").decode().strip()


def _save(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n")


def capture_baseline(container, workspace, output_dir):
    """Capture the trusted image workspace before the agent starts."""
    output = Path(output_dir).resolve()
    store = _new_store(output)
    with _docker_archive(container, workspace) as source:
        manifest, measured = _read_snapshot(source, store)
    tree = _tree(store, manifest)
    path = output / "baseline-manifest.json"
    _save(path, manifest)
    descriptor = {"version": 1, "store": str(store), "baseline_manifest": str(path),
                  "baseline_tree": tree, "limits": LIMITS, "exclusions": EXCLUSION_POLICY,
                  "baseline_measurements": measured}
    _save(output / "descriptor.json", descriptor)
    return descriptor


def _write_patch(store, first, last, destination):
    command = ["/usr/bin/git", "--git-dir=" + str(store), "-c", "core.hooksPath=/dev/null",
               "-c", "core.attributesFile=/dev/null", "diff-tree", "--no-commit-id", "-r", "-p",
               "--binary", "--full-index", "--no-renames", "--no-ext-diff", "--no-textconv",
               first, last]
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                               env=_environment(store), cwd=store.parent)
    timer = threading.Timer(LIMITS["seconds"], process.kill)
    timer.daemon = True
    timer.start()
    try:
        size = 0
        with open(destination, "xb") as stream:
            while chunk := process.stdout.read(65536):
                size += len(chunk)
                if size > LIMITS["patch_bytes"]:
                    raise SnapshotError("candidate patch byte limit exceeded")
                stream.write(chunk)
        if process.wait(timeout=5):
            raise SnapshotError("trusted patch generation failed or timed out")
    finally:
        timer.cancel()
        if process.poll() is None:
            process.kill()
        process.wait(timeout=5)
        process.stdout.close()


def _compare_snapshot(source, output, baseline):
    store = Path(baseline["store"])
    original = json.loads(Path(baseline["baseline_manifest"]).read_text())
    manifest, measured = _read_snapshot(source, store)
    ignored = sorted(name for name in manifest if name not in original and _new_cache(name))
    candidate = {name: row for name, row in manifest.items() if name not in ignored}
    tree = _tree(store, candidate)
    changed = sorted(name for name in set(original) | set(candidate) if original.get(name) != candidate.get(name))
    patch = output / "candidate.patch"
    _write_patch(store, baseline["baseline_tree"], tree, patch)
    # Verify the published patch represents the admitted bytes, not an
    # attribute-dependent presentation of them. This index is trusted and has
    # no candidate worktree, filters or hooks.
    _git(store, "read-tree", baseline["baseline_tree"])
    if patch.stat().st_size:
        _git(store, "apply", "--cached", "--binary", "--whitespace=nowarn", str(patch))
    if _git(store, "write-tree").decode().strip() != tree:
        raise SnapshotError("candidate patch does not reconstruct the snapshot tree")
    manifest_path = output / "candidate-manifest.json"
    _save(manifest_path, manifest)
    result = {"patch_path": str(patch), "patch_sha256": hashlib.sha256(patch.read_bytes()).hexdigest(),
              "changed_paths": changed, "existing_changed_paths": [name for name in changed if name in original],
              "ignored_new_cache_paths": ignored, "baseline_tree": baseline["baseline_tree"],
              "candidate_tree": tree, "baseline_manifest": baseline["baseline_manifest"],
              "candidate_manifest": str(manifest_path), "limits": LIMITS,
              "exclusions": EXCLUSION_POLICY, "candidate_measurements": measured}
    _save(output / "snapshot-result.json", result)
    return result


def capture_candidate_after_stop(container, workspace, output_dir, baseline):
    """Compare stopped candidate bytes; caller must not restart it during capture."""
    _require_stopped(container)
    output = Path(output_dir).resolve()
    output.mkdir(mode=0o700, parents=True, exist_ok=False)
    with _docker_archive(container, workspace) as source:
        return _compare_snapshot(source, output, baseline)


def _require_stopped(container):
    running = subprocess.check_output(["/usr/bin/docker", "inspect", "--format", "{{.State.Running}}", container],
                                      env=command_environment(),
                                      text=True, timeout=10).strip()
    if running != "false":
        raise SnapshotError("candidate must be stopped before workspace extraction")
