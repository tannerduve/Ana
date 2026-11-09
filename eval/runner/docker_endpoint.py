"""Explicit local Docker transport for evaluation, including SDK subprocesses.

The override is trusted host configuration, never candidate input. It selects a
local daemon; it does not change container permissions or provide a sandbox.
"""
import os
from pathlib import Path
import stat


def docker_host():
    value = os.environ.get("LEAN_HARNESS_DOCKER_HOST")
    if value is None:
        return None
    if (not value.startswith("unix:///") or any(c in value for c in "\x00\r\n?#%")
            or len(value[7:].encode()) > 107):
        raise ValueError("LEAN_HARNESS_DOCKER_HOST must name an absolute local Unix socket")
    path = Path(value[7:])
    if str(path) != value[7:] or ".." in path.parts or not stat.S_ISSOCK(path.stat().st_mode):
        raise ValueError("LEAN_HARNESS_DOCKER_HOST must name an existing local Unix socket")
    return value


def command_environment():
    # Do not propagate ambient transport overrides, API keys or startup hooks.
    env = {"PATH": os.defpath, "HOME": str(Path.home()), "LANG": "C.UTF-8"}
    selected = docker_host()
    if selected is not None:
        env.update(DOCKER_HOST=selected, LEAN_HARNESS_DOCKER_HOST=selected)
    return env
