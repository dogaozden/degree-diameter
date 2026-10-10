import os, sys
import pytest
from evolve.mutator import (extract_code, static_check, parse_stream, build_user_prompt, child_env,
                            MutationTask, FakeMutator, ClaudeMutator, BudgetStop)
from evolve.types import Case

CASES = [Case("d3D3", {"d": 3, "D": 3}, 14, 14, "calibration", 1)]
GOOD = "def build(d, D, seed, time_limit):\n    return 1, []\n"
TASK = MutationTask("g001-c00", "default", [("g000-seed", GOOD, {"d3D3": 14.0})], CASES)
FAKE = [sys.executable, os.path.join(os.path.dirname(__file__), "fake_claude.py")]

def test_extract_code_variants():
    assert extract_code("x\n```python\n" + GOOD + "```\nbye") == GOOD
    two = "```python\nimport os\n```\ntext\n```python\n" + GOOD + "```"
    assert extract_code(two) == GOOD
    assert extract_code("```\n" + GOOD + "```") == GOOD
    assert extract_code("```py\n" + GOOD + "```") == GOOD
    assert extract_code(GOOD) == GOOD.strip()
    assert extract_code("no code here") is None

def test_static_check():
    assert static_check(GOOD) is None
    assert static_check("def build(:\n").startswith("SyntaxError")
    assert static_check("def helper():\n    pass\n") == "no top-level def build(...)"

def test_prompt_contains_parent_scores_and_error():
    p = build_user_prompt(TASK)
    assert "### Parent g000-seed" in p and "d3D3" in p and "record 14" in p and GOOD in p
    p2 = build_user_prompt(TASK, previous_code="bad", error="SyntaxError: x")
    assert "### Your previous attempt failed" in p2 and "SyntaxError: x" in p2

def test_parse_stream():
    out = "\n".join([
        '{"type":"system","subtype":"init","apiKeySource":"none"}',
        'not json',
        '{"type":"rate_limit_event","rate_limit_info":{"unifiedWindows":{"seven_day":{"utilization":0.3}}}}',
        '{"type":"result","is_error":false,"result":"hi","usage":{"output_tokens":1},"total_cost_usd":0.01,"duration_api_ms":9,"modelUsage":{},"session_id":"s"}',
    ])
    r = parse_stream(out)
    assert r["auth"] == "none" and r["text"] == "hi" and not r["is_error"]
    assert r["rate_limits"]["seven_day"]["utilization"] == 0.3 and r["cost_usd"] == 0.01
    assert parse_stream("")["is_error"]

def test_child_env_strips_claude_vars(monkeypatch):
    monkeypatch.setenv("CLAUDE_CODE_SESSION", "x"); monkeypatch.setenv("ANTHROPIC_API_KEY", "k")
    monkeypatch.setenv("CLAUDE_CONFIG_DIR", "/c")
    e = child_env()
    assert "CLAUDE_CODE_SESSION" not in e and "ANTHROPIC_API_KEY" not in e
    assert e["CLAUDE_CONFIG_DIR"] == "/c" and e["CLAUDE_CODE_DISABLE_AUTO_MEMORY"] == "1"

def test_fake_mutator_retry_then_success():
    replies = {1: "sorry no code", 2: "```python\n" + GOOD + "```"}
    m = FakeMutator(lambda task, attempt: replies[attempt], smoke=lambda code: (True, ""))
    r = m.mutate(TASK)
    assert r.code == GOOD and r.attempts == 2 and r.error == ""

def test_fake_mutator_smoke_failure_twice():
    m = FakeMutator(lambda t, a: "```python\n" + GOOD + "```", smoke=lambda code: (False, "crash: boom"))
    r = m.mutate(TASK)
    assert r.code is None and r.attempts == 2 and "boom" in r.error

def test_claude_mutator_with_fake_cli(monkeypatch):
    monkeypatch.delenv("FAKE_CLAUDE_MODE", raising=False)
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    r = m.mutate(TASK)
    assert r.code.startswith("def build") and r.attempts == 1 and len(r.calls) == 1
    assert r.calls[0]["cost_usd"] == 0.001

def test_refuses_api_key(monkeypatch):
    monkeypatch.setenv("FAKE_CLAUDE_MODE", "apikey")
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    with pytest.raises(RuntimeError, match="refusing"):
        m.mutate(TASK)

def test_budget_stop_after_high_utilization(monkeypatch):
    monkeypatch.setenv("FAKE_CLAUDE_MODE", "limit90")
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    m.mutate(TASK)                       # this call succeeds but reports 95% use
    with pytest.raises(BudgetStop):
        m.mutate(TASK)

def test_usage_limit_is_budget_stop(monkeypatch):
    monkeypatch.setenv("FAKE_CLAUDE_MODE", "usage_limit")
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    with pytest.raises(BudgetStop) as e:
        m.mutate(TASK)
    assert len(e.value.calls) == 1

def test_transient_error_retried(monkeypatch, tmp_path):
    monkeypatch.setenv("FAKE_CLAUDE_MODE", "transient"); monkeypatch.setenv("FAKE_CLAUDE_COUNTER", str(tmp_path / "n"))
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE, backoff_s=(0.01,))
    r = m.mutate(TASK)
    assert r.code is not None and len(r.calls) == 2

def test_threaded_mutations_keep_their_own_call_records(monkeypatch):
    from concurrent.futures import ThreadPoolExecutor
    monkeypatch.delenv("FAKE_CLAUDE_MODE", raising=False)
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    tasks = [MutationTask(f"g001-c{i:02d}", "default", [("g000-seed", GOOD, {"d3D3": 14.0})], CASES)
             for i in range(24)]
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(m.mutate, tasks))
    assert len(results) == 24
    for task, r in zip(tasks, results):
        assert r.cid == task.cid and r.code is not None
        assert len(r.calls) == 1 and r.calls[0]["cid"] == task.cid
    assert sum(len(r.calls) for r in results) == 24

class FakePopen:
    """Stands in for subprocess.Popen: records the call, replies with canned output."""
    instances = []

    def __init__(self, cmd, canned_out="", canned_err="", returncode=0, timeout=False, **kw):
        self.cmd, self.kw, self._out, self._err = cmd, kw, canned_out, canned_err
        self.returncode, self._timeout, self.pid = returncode, timeout, 424242
        self.input = None
        self.killed = False
        FakePopen.instances.append(self)

    def communicate(self, input=None, timeout=None):
        import subprocess
        if input is not None:
            self.input = input
        if self._timeout and not self.killed:
            raise subprocess.TimeoutExpired(self.cmd, timeout)
        return self._out, self._err


def popen_factory(**canned):
    FakePopen.instances = []
    return lambda cmd, **kw: FakePopen(cmd, **canned, **kw)


def test_exact_argv_cwd_env_and_stdin(monkeypatch):
    import evolve.mutator as mut
    stdout = "\n".join([
        '{"type":"system","subtype":"init","apiKeySource":"none"}',
        '{"type":"result","is_error":false,"result":"ok","usage":{},"total_cost_usd":0,"duration_api_ms":1}',
    ])
    monkeypatch.setenv("ANTHROPIC_API_KEY", "k")
    monkeypatch.setattr(mut.subprocess, "Popen", popen_factory(canned_out=stdout))
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli="claude")
    m.call("the prompt")
    proc = FakePopen.instances[0]
    assert proc.cmd == ["claude", "-p", "--output-format", "stream-json", "--verbose",
                        "--model", "claude-haiku-5-5", "--setting-sources", "",
                        "--strict-mcp-config", "--disable-slash-commands", "--tools", "",
                        "--system-prompt=sys"]
    kw = proc.kw
    assert str(kw["cwd"]).endswith(".cache/claude-p-isolated")
    assert "ANTHROPIC_API_KEY" not in kw["env"] and kw["env"]["CLAUDE_CODE_DISABLE_AUTO_MEMORY"] == "1"
    assert kw["start_new_session"] is True
    assert proc.input == "the prompt"

def test_failed_cli_run_reports_real_error(monkeypatch):
    import evolve.mutator as mut
    monkeypatch.setattr(mut.subprocess, "Popen", popen_factory(returncode=3, canned_err="x" * 2000 + "kaboom"))
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli="claude")
    r = m.mutate(TASK)
    prompts = [p.input for p in FakePopen.instances]
    assert r.code is None and r.attempts == 2 and len(r.calls) == 2
    assert r.error.startswith("claude -p failed: no result event (exit code 3)") and r.error.endswith("kaboom")
    assert len(r.error) < 1200
    assert "claude -p failed" in prompts[1] and "no python code block" not in prompts[1]

def test_timeout_kills_the_whole_process_group(monkeypatch):
    import evolve.mutator as mut
    kills = []
    def fake_killpg(pgid, sig):
        kills.append((pgid, sig))
        FakePopen.instances[-1].killed = True
    monkeypatch.setattr(mut.os, "killpg", fake_killpg)
    monkeypatch.setattr(mut.subprocess, "Popen", popen_factory(timeout=True))
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli="claude", timeout_s=0.01)
    res = m.call("p")
    import signal
    assert res["is_error"] and res["error_message"] == "timeout"
    assert kills == [(424242, signal.SIGKILL)]

def test_abort_makes_next_mutate_raise_without_running_a_process(monkeypatch):
    import evolve.mutator as mut
    monkeypatch.setattr(mut.subprocess, "Popen", popen_factory())
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli="claude")
    m.abort()
    with pytest.raises(BudgetStop, match="aborted"):
        m.mutate(TASK)
    assert FakePopen.instances == []

def test_abort_stops_the_retry_attempt(monkeypatch):
    monkeypatch.delenv("FAKE_CLAUDE_MODE", raising=False)
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    real_call, n = m.call, []
    def call_then_abort(prompt, runs=None):
        res = real_call(prompt, runs)
        n.append(1)
        m.abort()
        res["text"] = "no code in this reply"    # force a retry
        return res
    m.call = call_then_abort
    with pytest.raises(BudgetStop, match="aborted") as e:
        m.mutate(TASK)
    assert len(n) == 1 and len(e.value.calls) == 1

def test_prompt_shows_why_a_parent_scored_zero():
    cases = [Case("d7D4", {"d": 7, "D": 4}, 346, 518, "target", 2),
             Case("d4D3", {"d": 4, "D": 3}, 62, 62, "calibration", 1),
             Case("d3D3", {"d": 3, "D": 3}, 14, 14, "calibration", 1),
             Case("d5D3", {"d": 5, "D": 3}, 62, 62, "calibration", 1)]
    scores = {"d7D4": {"value": 0.0, "status": "timeout", "reason": "timeout: killed after 20.0s"},
              "d4D3": {"value": 0.0, "status": "ok", "reason": "degree: vertex 7 has 5 > 4 " + "x" * 200},
              "d3D3": 14.0,
              "d5D3": {"value": 30.0, "status": "ok", "reason": ""}}
    task = MutationTask("g001-c00", "default", [("g000-seed", GOOD, scores)], cases, time_limit=15)
    p = build_user_prompt(task)
    assert "d7D4 (target, d=7, D=4): 0 [timeout] / record 346 / ceiling 518" in p
    assert "d4D3 (calibration, d=4, D=3): 0 [invalid: degree: vertex 7 has 5 > 4 " in p
    assert "x" * 81 not in p
    assert "d3D3 (calibration, d=3, D=3): 14 / record 14" in p
    assert "d5D3 (calibration, d=5, D=3): 30 / record 62" in p
    assert "Each case gets 15 seconds." in p

def test_crashed_parent_case_shows_the_error_tail():
    cases = [Case("d3D3", {"d": 3, "D": 3}, 14, 14, "calibration", 1)]
    scores = {"d3D3": {"value": 0.0, "status": "crash",
                       "reason": "crash: Traceback (most recent call last):\n  File x\nValueError: boom"}}
    p = build_user_prompt(MutationTask("c", "default", [("p", GOOD, scores)], cases))
    assert "d3D3 (calibration, d=3, D=3): 0 [crash: ValueError: boom] / record 14" in p
    assert "Each case gets" not in p

def test_crossover_with_one_parent_uses_default_instruction():
    from evolve.mutator import ROLE_INSTRUCTIONS
    one = MutationTask("c", "crossover", [("p", GOOD, {})], CASES)
    p = build_user_prompt(one)
    assert p.startswith(ROLE_INSTRUCTIONS["default"]) and "two parent programs" not in p
    two = MutationTask("c", "crossover", [("p", GOOD, {}), ("q", GOOD, {})], CASES)
    assert build_user_prompt(two).startswith(ROLE_INSTRUCTIONS["crossover"])

def test_call_records_carry_auth_and_model_usage(monkeypatch):
    monkeypatch.delenv("FAKE_CLAUDE_MODE", raising=False)
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    rec = m.mutate(TASK).calls[0]
    assert rec["auth"] == "none"
    assert rec["model_usage"] == {"claude-haiku-5-5": {"outputTokens": 5}}

def test_real_timeout_kills_child_and_grandchild(monkeypatch, tmp_path):
    import time
    pidfile = tmp_path / "pid"
    monkeypatch.setenv("FAKE_CLAUDE_MODE", "hang"); monkeypatch.setenv("FAKE_CLAUDE_PIDFILE", str(pidfile))
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE, timeout_s=1.5)
    t0 = time.time()
    res = m.call("p")
    assert res["error_message"] == "timeout" and time.time() - t0 < 10
    pid = int(pidfile.read_text())
    for _ in range(50):
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            break
        time.sleep(0.1)
    else:
        raise AssertionError("grandchild still alive")
