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

def test_exact_argv_cwd_env_and_stdin(monkeypatch):
    import subprocess
    import evolve.mutator as mut
    seen = {}
    stdout = "\n".join([
        '{"type":"system","subtype":"init","apiKeySource":"none"}',
        '{"type":"result","is_error":false,"result":"ok","usage":{},"total_cost_usd":0,"duration_api_ms":1}',
    ])
    def fake_run(cmd, **kw):
        seen["cmd"], seen["kw"] = cmd, kw
        return subprocess.CompletedProcess(cmd, 0, stdout, "")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "k")
    monkeypatch.setattr(mut.subprocess, "run", fake_run)
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli="claude")
    m.call("the prompt")
    assert seen["cmd"] == ["claude", "-p", "--output-format", "stream-json", "--verbose",
                           "--model", "claude-haiku-5-5", "--setting-sources", "",
                           "--strict-mcp-config", "--disable-slash-commands", "--tools", "",
                           "--system-prompt=sys"]
    kw = seen["kw"]
    assert str(kw["cwd"]).endswith(".cache/claude-p-isolated")
    assert "ANTHROPIC_API_KEY" not in kw["env"] and kw["env"]["CLAUDE_CODE_DISABLE_AUTO_MEMORY"] == "1"
    assert kw["input"] == "the prompt"

def test_failed_cli_run_reports_real_error(monkeypatch):
    import subprocess
    import evolve.mutator as mut
    prompts = []
    def fake_run(cmd, **kw):
        prompts.append(kw["input"])
        return subprocess.CompletedProcess(cmd, 3, "", "x" * 2000 + "kaboom")
    monkeypatch.setattr(mut.subprocess, "run", fake_run)
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli="claude")
    r = m.mutate(TASK)
    assert r.code is None and r.attempts == 2 and len(r.calls) == 2
    assert r.error.startswith("claude -p failed: no result event (exit code 3)") and r.error.endswith("kaboom")
    assert len(r.error) < 1200
    assert "claude -p failed" in prompts[1] and "no python code block" not in prompts[1]
