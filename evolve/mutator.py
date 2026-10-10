"""Mutator: asks Claude Haiku (via headless `claude -p`) for a new version of a program."""
from __future__ import annotations

import json
import os
import re
import subprocess
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from evolve.types import Case


class BudgetStop(Exception):
    def __init__(self, message: str, calls: list[dict] | None = None):
        super().__init__(message)
        self.calls: list[dict] = calls if calls is not None else []


@dataclass
class MutationTask:
    cid: str
    role: str                                   # "default" | "crossover" | "invent" | "moonshot"
    parents: list[tuple[str, str, dict]]        # (parent cid, code, {case_id: value})
    cases: list[Case]


@dataclass
class MutationResult:
    cid: str
    code: str | None
    attempts: int
    calls: list[dict]
    error: str                                  # "" on success


ROLE_INSTRUCTIONS: dict[str, str] = {
    "default": "Improve the parent program so it scores higher on more cases, especially the targets. "
               "Make a focused, meaningful change.",
    "crossover": "You are given two parent programs. Combine their strongest ideas into one program "
                 "that beats both.",
    "invent": "Invent a new construction idea or helper routine that the parent does not use yet, "
              "implement it inside the program, and use it where it helps.",
    "moonshot": "Make a bold, high-risk change: try a substantially different construction for the "
                "cases where the parent is weakest. Keep a safe fallback so every case still returns "
                "a valid graph.",
}

_FINAL_LINE = ("Reply with the complete new program in a single ```python code block. "
               "Do not include anything after the code block.")


def _case_line(case: Case, scores: dict) -> str:
    params = ", ".join(f"{k}={v}" for k, v in case.params.items())
    value = scores.get(case.id)
    shown = "not scored" if value is None else f"{value:g}"
    return (f"{case.id} ({case.kind}, {params}): {shown} / record {case.record:g} "
            f"/ ceiling {case.ceiling:g}")


def build_user_prompt(task: MutationTask, previous_code: str | None = None,
                      error: str | None = None) -> str:
    parts = [ROLE_INSTRUCTIONS[task.role]]
    for cid, code, scores in task.parents:
        lines = "\n".join(_case_line(c, scores) for c in task.cases)
        parts.append(f"### Parent {cid}\n\nScores:\n{lines}\n\n```python\n{code}\n```")
    if error:
        parts.append("### Your previous attempt failed\n\n"
                     f"```python\n{previous_code or ''}\n```\n\nError:\n{error}")
    parts.append(_FINAL_LINE)
    return "\n\n".join(parts)


_FENCE = re.compile(r"```(?:python|py)?[ \t]*\n(.*?)```", re.DOTALL)


def extract_code(text: str) -> str | None:
    blocks = [m.group(1) for m in _FENCE.finditer(text) if "def build" in m.group(1)]
    if blocks:
        return blocks[-1]
    stripped = text.strip()
    if stripped.startswith(("def build", "import")):
        try:
            compile(stripped, "candidate.py", "exec")
        except (SyntaxError, ValueError):
            return None
        return stripped
    return None


def static_check(code: str) -> str | None:
    try:
        compile(code, "candidate.py", "exec")
    except SyntaxError as e:
        return f"SyntaxError: {e.msg} (line {e.lineno})"
    except ValueError as e:
        return f"ValueError: {e}"
    if not re.search(r"^def build\(", code, re.M):
        return "no top-level def build(...)"
    return None


def parse_stream(stdout: str) -> dict:
    init = result = rate = None
    for line in stdout.splitlines():
        try:
            ev = json.loads(line)
        except ValueError:
            continue
        if not isinstance(ev, dict):
            continue
        kind = ev.get("type")
        if kind == "system" and ev.get("subtype") == "init" and init is None:
            init = ev
        elif kind == "result":
            result = ev
        elif kind == "rate_limit_event":
            rate = ev
    out = {"text": "", "is_error": True, "error_status": None, "error_message": "no result event",
           "usage": {}, "cost_usd": 0.0, "duration_api_ms": 0, "auth": None,
           "rate_limits": {}, "model_usage": {}, "session_id": None}
    if init is not None:
        out["auth"] = init.get("apiKeySource")
    if rate is not None:
        out["rate_limits"] = (rate.get("rate_limit_info") or {}).get("unifiedWindows") or {}
    if result is not None:
        is_error = bool(result.get("is_error"))
        out.update(
            text=result.get("result") or "",
            is_error=is_error,
            error_status=result.get("api_error_status"),
            error_message=(result.get("result") or result.get("subtype") or "error") if is_error else "",
            usage=result.get("usage") or {},
            cost_usd=result.get("total_cost_usd") or 0.0,
            duration_api_ms=result.get("duration_api_ms") or 0,
            model_usage=result.get("modelUsage") or {},
            session_id=result.get("session_id"),
        )
    return out


def child_env() -> dict:
    keep = {"CLAUDE_CONFIG_DIR", "CLAUDE_CODE_OAUTH_TOKEN"}
    env = {k: v for k, v in os.environ.items()
           if k in keep or not k.startswith(("CLAUDE", "ANTHROPIC"))}
    env["CLAUDE_CODE_DISABLE_AUTO_MEMORY"] = "1"
    return env


def _check(code: str | None, smoke: Callable[[str], tuple[bool, str]]) -> str | None:
    if code is None:
        return "no python code block found"
    err = static_check(code)
    if err is not None:
        return err
    ok, msg = smoke(code)
    return None if ok else (msg or "smoke test failed")


class _CallFailed(Exception):
    """A CLI call produced no usable reply (timeout, exhausted retries, non-transient error)."""


def _mutate_with(get_reply: Callable[[str], str], task: MutationTask, smoke,
                 calls: list[dict] | None = None) -> MutationResult:
    """Shared attempt/retry flow: one attempt, then one retry that shows the model its failure.

    get_reply may raise _CallFailed; that attempt then fails with the real CLI error text.
    """
    calls = calls if calls is not None else []

    def attempt(prompt: str) -> tuple[str | None, str, str | None]:
        try:
            reply = get_reply(prompt)
        except _CallFailed as e:
            return None, "", str(e)
        code = extract_code(reply)
        return code, reply, _check(code, smoke)

    try:
        code, reply, err = attempt(build_user_prompt(task))
        attempts = 1
        if err is not None:
            prompt = build_user_prompt(task, previous_code=code or reply[:4000], error=err)
            code, reply, err = attempt(prompt)
            attempts = 2
    except BudgetStop as e:
        e.calls = calls
        raise
    return MutationResult(task.cid, None if err else code, attempts, calls, err or "")


_LIMIT_RE = re.compile(r"usage limit|limit reached|hit your (\w+ )?limit", re.I)


class ClaudeMutator:
    def __init__(self, model: str, system_prompt: str, smoke, timeout_s: float = 300.0,
                 stop_at: float = 0.9, cli: str | list[str] = "claude", backoff_s: tuple = (2, 8, 30)):
        self.model = model
        self.system_prompt = system_prompt
        self.smoke = smoke
        self.timeout_s = timeout_s
        self.stop_at = stop_at
        self.cli = [cli] if isinstance(cli, str) else list(cli)
        self.backoff_s = tuple(backoff_s)
        self._limit_hit = False
        self._rate_limits: dict = {}
        self._lock = threading.Lock()       # guards _limit_hit and _rate_limits (shared across threads)

    def _max_utilization(self) -> float:
        # caller holds self._lock
        vals = [w.get("utilization") for w in self._rate_limits.values() if isinstance(w, dict)]
        return max((v for v in vals if isinstance(v, (int, float))), default=0.0)

    def _run_once(self, prompt: str) -> dict:
        cwd = Path.home() / ".cache" / "claude-p-isolated"
        cwd.mkdir(parents=True, exist_ok=True)
        cmd = self.cli + ["-p", "--output-format", "stream-json", "--verbose",
                          "--model", self.model, "--setting-sources", "",
                          "--strict-mcp-config", "--disable-slash-commands", "--tools", "",
                          f"--system-prompt={self.system_prompt}"]
        t0 = time.monotonic()
        try:
            proc = subprocess.run(cmd, input=prompt, capture_output=True, text=True,
                                  timeout=self.timeout_s, cwd=cwd, env=child_env())
            res = parse_stream(proc.stdout)
            if res["error_message"] == "no result event":
                res["error_message"] += f" (exit code {proc.returncode}): {(proc.stderr or '')[-1000:]}"
        except subprocess.TimeoutExpired:
            res = parse_stream("")
            res["error_message"] = "timeout"
        res["wall_s"] = time.monotonic() - t0
        return res

    def call(self, prompt: str, runs: list[dict] | None = None) -> dict:
        """One logical CLI call (with transient retries). Every CLI run is appended to `runs`."""
        runs = runs if runs is not None else []
        with self._lock:
            if self._limit_hit or self._max_utilization() >= self.stop_at:
                raise BudgetStop("subscription budget reached before call")
        retries = 0
        while True:
            res = self._run_once(prompt)
            runs.append(res)
            with self._lock:
                if res["rate_limits"]:
                    self._rate_limits = res["rate_limits"]
            auth = res["auth"]
            if auth is not None and auth != "none":
                raise RuntimeError("refusing: claude -p is not using the subscription login "
                                   f"(apiKeySource={auth})")
            if res["is_error"] and _LIMIT_RE.search(res["error_message"] or ""):
                with self._lock:
                    self._limit_hit = True
                raise BudgetStop(f"subscription limit hit: {res['error_message']}")
            status = res["error_status"]
            transient = isinstance(status, int) and (status in (429, 529) or status >= 500)
            if res["is_error"] and transient and retries < len(self.backoff_s):
                time.sleep(self.backoff_s[retries])
                retries += 1
                continue
            break
        if not res["is_error"]:
            with self._lock:
                if self._max_utilization() >= self.stop_at:
                    self._limit_hit = True
        return res

    def mutate(self, task: MutationTask) -> MutationResult:
        calls: list[dict] = []
        attempt = 0

        def get_reply(prompt: str) -> str:
            nonlocal attempt
            attempt += 1
            runs: list[dict] = []
            try:
                res = self.call(prompt, runs)
            finally:
                for raw in runs:
                    calls.append({
                        "cid": task.cid, "attempt": attempt, "model": self.model,
                        "usage": raw["usage"], "cost_usd": raw["cost_usd"],
                        "duration_api_ms": raw["duration_api_ms"], "wall_s": raw["wall_s"],
                        "is_error": raw["is_error"], "error_message": raw["error_message"],
                        "rate_limits": raw["rate_limits"],
                    })
            if res["is_error"]:
                raise _CallFailed(f"claude -p failed: {res['error_message']}")
            return res["text"]

        return _mutate_with(get_reply, task, self.smoke, calls)


class FakeMutator:
    def __init__(self, reply: Callable[[MutationTask, int], str], smoke):
        self.reply = reply
        self.smoke = smoke

    def mutate(self, task: MutationTask) -> MutationResult:
        attempt = 0

        def get_reply(prompt: str) -> str:
            nonlocal attempt
            attempt += 1
            return self.reply(task, attempt)

        return _mutate_with(get_reply, task, self.smoke)
