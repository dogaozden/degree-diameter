"""Run one untrusted program on one case in its own process group, with a hard wall-clock limit."""
from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

HARNESS = Path(__file__).with_name("_harness.py")
_THREAD_VARS = ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS")


@dataclass
class RunResult:
    status: str          # "ok" | "timeout" | "crash" | "bad_output"
    output: object       # parsed JSON from build(), None unless status == "ok"
    wall_s: float
    error: str           # "" on ok; else the last 2000 chars of stderr or a message


def _kill_group(pgid: int) -> None:
    try:
        os.killpg(pgid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def run_program(program: Path, harness_dir: Path, params: dict, seed: int,
                time_limit: float, grace_s: float = 5.0) -> RunResult:
    env = dict(os.environ)
    env.update({v: "1" for v in _THREAD_VARS})
    with tempfile.TemporaryDirectory(prefix="evolve-run-") as tmp:
        out_path = Path(tmp) / "out.json"
        err_path = Path(tmp) / "stderr.txt"
        # cwd is the temp dir, so the child needs absolute paths
        cmd = [sys.executable, "-I", str(HARNESS), str(Path(program).resolve()), str(Path(harness_dir).resolve()),
               json.dumps(params), str(seed), str(time_limit), str(out_path)]
        start = time.monotonic()
        with open(err_path, "wb") as err_f:
            proc = subprocess.Popen(cmd, cwd=tmp, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                    stderr=err_f, start_new_session=True)
            try:
                try:
                    code = proc.wait(timeout=time_limit + grace_s)
                except subprocess.TimeoutExpired:
                    _kill_group(proc.pid)
                    proc.wait()
                    return RunResult("timeout", None, time.monotonic() - start,
                                     f"killed after {time_limit + grace_s:.1f}s wall-clock limit")
            finally:
                _kill_group(proc.pid)   # reap any children the program left behind
        wall = time.monotonic() - start
        stderr = err_path.read_text(errors="replace")[-2000:]
        if code == 0:
            try:
                return RunResult("ok", json.loads(out_path.read_text()), wall, "")
            except (OSError, ValueError) as e:
                return RunResult("bad_output", None, wall, f"unreadable output file: {e}")
        if code == 2:
            return RunResult("bad_output", None, wall, stderr or "output not serializable")
        return RunResult("crash", None, wall, stderr or f"exit code {code}")
