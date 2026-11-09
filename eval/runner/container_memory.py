"""Bounded cgroup-v2 sampling for the candidate container, not wrapper RSS."""
from pathlib import Path
import re
import subprocess
import threading
import time
from docker_endpoint import command_environment


_DIAGNOSTIC_BYTES = 16384
_BASE_EVENT_KEYS = {"low", "high", "max", "oom", "oom_kill"}


def _counter(text):
    if not re.fullmatch(r"[0-9]{1,20}", text) or int(text) > 2**64 - 1:
        raise ValueError("invalid unsigned counter")
    return int(text)


def _events(text):
    values = {}
    lines = text.splitlines()
    if len(lines) > 64:
        raise ValueError("too many memory.events fields")
    for line in lines:
        fields = line.split()
        if len(fields) != 2 or not re.fullmatch(r"[a-z][a-z0-9_]*", fields[0]):
            raise ValueError("malformed memory.events field")
        name, value = fields
        if name in values:
            raise ValueError("duplicate memory.events field")
        values[name] = _counter(value)
    if not _BASE_EVENT_KEYS <= values.keys():
        raise ValueError("missing memory.events field")
    return values


class ContainerMemory:
    def __init__(self, container, interval_seconds=0.1):
        self.container = container
        self.interval = interval_seconds
        self.stop_event = threading.Event()
        self.thread = None
        self.path = None
        self.samples = 0
        self.baseline = None
        self.peak = None
        self.error = None
        self.started = None
        self.diagnostic_lock = threading.Lock()
        self.diagnostics = {
            name: {"before": None, "final": None, "last_observed": None,
                   "first_observation_problem": None}
            for name in ("memory.events", "memory.max")}

    def _observe(self, name):
        observation = {"observed_at_unix": time.time(),
                       "elapsed_seconds": time.monotonic() - self.started if self.started is not None else None,
                       "value": None, "unknown_reason": None}
        try:
            if self.path is None:
                raise ValueError("candidate cgroup could not be located")
            with self.path.with_name(name).open("rb") as stream:
                raw = stream.read(_DIAGNOSTIC_BYTES + 1)
            if len(raw) > _DIAGNOSTIC_BYTES:
                raise ValueError("diagnostic byte limit exceeded")
            text = raw.decode("ascii").strip()
            observation["value"] = (_events(text) if name == "memory.events" else
                                    "max" if text == "max" else _counter(text))
        except (OSError, UnicodeError, ValueError) as error:
            observation["unknown_reason"] = f"{type(error).__name__}: {name} unavailable or invalid"
        return observation

    def _sample_diagnostics(self, final=False):
        observations = {name: self._observe(name) for name in self.diagnostics}
        with self.diagnostic_lock:
            for name, current in observations.items():
                record = self.diagnostics[name]
                previous = record["last_observed"]
                problem = current["unknown_reason"]
                if name == "memory.events" and problem is None and previous is not None:
                    old, new = previous["value"], current["value"]
                    if old.keys() != new.keys():
                        problem = "memory.events fields changed during observation"
                    elif any(new[key] < old[key] for key in old):
                        problem = "memory.events counter decreased during observation"
                if record["first_observation_problem"] is None and problem is not None:
                    record["first_observation_problem"] = problem
                if final:
                    record["final"] = current
                elif record["before"] is None:
                    record["before"] = current
                if current["unknown_reason"] is None:
                    record["last_observed"] = current

    def _diagnostic_report(self, sampler_still_running):
        with self.diagnostic_lock:
            records = {name: dict(record) for name, record in self.diagnostics.items()}
        for record in records.values():
            for stage in ("before", "final"):
                if record[stage] is None:
                    record[stage] = {"observed_at_unix": None, "elapsed_seconds": None,
                                     "value": None, "unknown_reason":
                                     "sampler did not stop; final observation unavailable"
                                     if stage == "final" and sampler_still_running else
                                     f"{stage} observation unavailable"}
        events = records["memory.events"]
        before, final = events["before"], events["final"]
        problem = events["first_observation_problem"]
        if sampler_still_running:
            problem = "sampler did not stop; final observation unavailable"
        else:
            problem = problem or before["unknown_reason"] or final["unknown_reason"]
        events["delta"] = None
        events["delta_unknown_reason"] = problem
        if problem is None:
            # All observations were valid, with unchanged keys and no decrease.
            events["delta"] = {key: final["value"][key] - value
                               for key, value in before["value"].items()}
        return {"method": "bounded cgroup-v2 memory.events and memory.max reads",
                "scope": "candidate cgroup; memory.events normally includes descendants "
                         "unless memory_localevents is enabled",
                "interpretation": "oom_kill counts processes killed by any OOM killer. "
                                  "Counters do not identify an OOM victim or prove the cause of exit 137. "
                                  "Unknown diagnostics do not imply unknown provider charges.",
                "memory_events": events, "memory_max": records["memory.max"]}

    def _sample(self):
        try:
            value = int(self.path.read_text().strip())
            if value < 0:
                raise ValueError("negative memory.current")
            if self.baseline is None:
                self.baseline = value
            self.peak = value if self.peak is None else max(self.peak, value)
            self.samples += 1
        except (OSError, ValueError) as error:
            self.error = f"{type(error).__name__}: candidate cgroup memory.current unavailable"
            self.stop_event.set()
        self._sample_diagnostics()

    def start(self):
        self.started = time.monotonic()
        try:
            pid = int(subprocess.check_output(["docker", "inspect", "--format", "{{.State.Pid}}", self.container],
                                             text=True, timeout=10, env=command_environment()))
            if pid <= 0:
                raise ValueError("candidate container is not running")
            entries = Path(f"/proc/{pid}/cgroup").read_text().splitlines()
            relative = next(line[3:] for line in entries if line.startswith("0::"))
            self.path = Path("/sys/fs/cgroup") / relative.lstrip("/") / "memory.current"
            self._sample()
            if self.error is None:
                self.thread = threading.Thread(target=self._loop, daemon=True)
                self.thread.start()
        except (OSError, ValueError, StopIteration, subprocess.SubprocessError):
            self.error = "host-visible cgroup-v2 memory.current could not be located"
        return self

    def _loop(self):
        while not self.stop_event.wait(self.interval):
            self._sample()

    def stop(self):
        self.stop_event.set()
        if self.thread is not None:
            self.thread.join(timeout=1)
        sampler_still_running = self.thread is not None and self.thread.is_alive()
        if not sampler_still_running:
            self._sample_diagnostics(final=True)
        return {"method": "sampled cgroup-v2 memory.current", "scope": "whole candidate container during agent invocation",
                "includes_page_cache": True, "is_process_rss": False,
                "sampling_interval_seconds": self.interval, "samples": self.samples,
                "baseline_bytes": self.baseline, "sampled_peak_bytes": self.peak,
                "elapsed_seconds": round(time.monotonic() - self.started, 3) if self.started is not None else None,
                "unavailable_reason": self.error,
                "cgroup_diagnostics": self._diagnostic_report(sampler_still_running)}
