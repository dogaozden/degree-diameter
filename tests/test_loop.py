import json
from pathlib import Path
import pytest
from evolve.config import load_config, RunConfig
from evolve.loop import run, EXIT_DONE, EXIT_BUDGET, EXIT_CHECKER_BUG
from evolve.mutator import FakeMutator, BudgetStop, MutationResult

def cfg(**kw):
    base = dict(run_id="t", problem="tests.toy_problem", seed=1, generations=2, candidates_per_generation=3,
                eval_seeds=[0], time_limit_s=5, workers=2,
                mutator={"kind": "fake", "concurrency": 2, "max_calls": 100},
                selection={"elite_k": 2, "roles": {"default": 1.0}}, git={"enabled": False, "push": False})
    base.update(kw); return RunConfig(**base)

def better(task, attempt):   # returns x*2+1 → beats records (6 and 10) by 1
    return "```python\nimport helper\ndef build(x, seed, time_limit):\n    return helper.double(x) + 1\n```"

def ok_smoke(code): return (True, "")

def test_load_config_files():
    c, text = load_config("configs/pilot.toml")
    assert c.mutator["model"] == "claude-haiku-5-5" and c.generations >= 1 and "pilot" in text
    s, _ = load_config("configs/smoke.toml")
    assert s.git["enabled"] is False

def test_full_run_and_records(tmp_path):
    rc = run(cfg(), "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None)
    assert rc == EXIT_DONE
    root = tmp_path / "runs" / "t"
    for g in range(3):
        assert json.loads((root / "generations" / f"{g:03d}.json").read_text())["complete"]
    assert len(list((root / "candidates").iterdir())) == 1 + 3 + 3
    s1 = json.loads((root / "generations" / "001.json").read_text())
    assert s1["best_by_case"]["c2"]["value"] == 11 and ["c2", s1["best_by_case"]["c2"]["cid"], 11] in s1["new_records"]
    assert list((tmp_path / "records" / "toy" / "c2").glob("11-t-*.json"))
    assert "NEW" in (root / "status.md").read_text()

class Crashy:
    def __init__(self, n): self.n = n; self.inner = FakeMutator(better, ok_smoke)
    def mutate(self, task):
        self.n -= 1
        if self.n < 0: raise KeyboardInterrupt
        return self.inner.mutate(task)

def test_resume_after_crash(tmp_path):
    c = cfg(mutator={"kind": "fake", "concurrency": 1, "max_calls": 100})
    with pytest.raises(KeyboardInterrupt):
        run(c, "x", tmp_path, mutator=Crashy(4), log=lambda *a: None)
    assert run(c, "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None) == EXIT_DONE
    root = tmp_path / "runs" / "t"
    cids = sorted(p.name for p in (root / "candidates").iterdir())
    assert cids == ["g000-seed", "g001-c00", "g001-c01", "g001-c02", "g002-c00", "g002-c01", "g002-c02"]
    assert all((root / "candidates" / cid / "result.json").exists() for cid in cids)

class Budgety:
    def __init__(self): self.n = 0; self.inner = FakeMutator(better, ok_smoke)
    def mutate(self, task):
        self.n += 1
        if self.n == 3: raise BudgetStop("limit", calls=[{"cid": task.cid}])
        return self.inner.mutate(task)

def test_budget_stop_then_resume(tmp_path):
    c = cfg(mutator={"kind": "fake", "concurrency": 1, "max_calls": 100})
    assert run(c, "x", tmp_path, mutator=Budgety(), log=lambda *a: None) == EXIT_BUDGET
    root = tmp_path / "runs" / "t"
    assert json.loads((root / "generations" / "001.json").read_text())["complete"] is False
    assert run(c, "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None) == EXIT_DONE
    assert json.loads((root / "generations" / "001.json").read_text())["complete"] is True

def test_max_calls_stops(tmp_path):
    class Counting:
        def __init__(self): self.inner = FakeMutator(better, ok_smoke)
        def mutate(self, task):
            r = self.inner.mutate(task); r.calls = [{"cid": task.cid}]; return r
    c = cfg(mutator={"kind": "fake", "concurrency": 1, "max_calls": 2})
    assert run(c, "x", tmp_path, mutator=Counting(), log=lambda *a: None) == EXIT_BUDGET

def test_checker_bug_exit(tmp_path):
    huge = lambda t, a: "```python\ndef build(x, seed, time_limit):\n    return 1000\n```"
    assert run(cfg(), "x", tmp_path, mutator=FakeMutator(huge, ok_smoke), log=lambda *a: None) == EXIT_CHECKER_BUG

def test_failed_mutations_counted(tmp_path):
    nocode = lambda t, a: "no code"
    assert run(cfg(generations=1), "x", tmp_path, mutator=FakeMutator(nocode, ok_smoke), log=lambda *a: None) == EXIT_DONE
    s = json.loads((tmp_path / "runs" / "t" / "generations" / "001.json").read_text())
    assert s["made"] == 0 and s["failed"] == 3

def test_invalid_case_records_zero_value_and_score(tmp_path):
    bad = lambda t, a: "```python\ndef build(x, seed, time_limit):\n    return 'nope'\n```"
    c = cfg(generations=1, candidates_per_generation=1)
    # the smoke test would reject this code, so use the always-ok smoke and let evaluation score it
    assert run(c, "x", tmp_path, mutator=FakeMutator(bad, ok_smoke), log=lambda *a: None) == EXIT_DONE
    res = json.loads((tmp_path / "runs" / "t" / "candidates" / "g001-c00" / "result.json").read_text())
    for case in res["cases"].values():
        assert case["valid"] is False and case["value"] == 0.0 and case["score"] == 0.0

def test_crashing_program_scores_zero(tmp_path):
    boom = lambda t, a: "```python\ndef build(x, seed, time_limit):\n    raise ValueError('boom')\n```"
    c = cfg(generations=1, candidates_per_generation=1)
    assert run(c, "x", tmp_path, mutator=FakeMutator(boom, ok_smoke), log=lambda *a: None) == EXIT_DONE
    res = json.loads((tmp_path / "runs" / "t" / "candidates" / "g001-c00" / "result.json").read_text())
    assert all(v["status"] == "crash" and v["value"] == 0.0 and v["score"] == 0.0 for v in res["cases"].values())

def test_restart_reuses_saved_plan(tmp_path):
    c = cfg(generations=1, mutator={"kind": "fake", "concurrency": 1, "max_calls": 100})
    run(c, "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None)
    plan_path = tmp_path / "runs" / "t" / "generations" / "001.plan.json"
    plan = json.loads(plan_path.read_text())
    plan["tasks"][0]["role"] = "sentinel"
    plan_path.write_text(json.dumps(plan))
    (tmp_path / "runs" / "t" / "generations" / "001.json").unlink()
    run(c, "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None)
    assert json.loads(plan_path.read_text())["tasks"][0]["role"] == "sentinel"

def test_record_file_only_saved_when_higher(tmp_path):
    run(cfg(), "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None)
    # every g001 and g002 candidate scores 11 on c2, but only the first one writes a file
    assert len(list((tmp_path / "records" / "toy" / "c2").glob("11-t-*.json"))) == 1

def test_second_checker_disagreement_invalidates(tmp_path, monkeypatch):
    from tests.toy_problem import PROBLEM
    monkeypatch.setattr(PROBLEM, "verify", lambda case, output: False)
    run(cfg(generations=1, candidates_per_generation=1), "x", tmp_path,
        mutator=FakeMutator(better, ok_smoke), log=lambda *a: None)
    res = json.loads((tmp_path / "runs" / "t" / "candidates" / "g001-c00" / "result.json").read_text())
    assert res["cases"]["c2"]["valid"] is False and res["cases"]["c2"]["reason"] == "second checker disagreed"
    assert not (tmp_path / "records").exists()

def test_cli_status_and_run(tmp_path, capsys, monkeypatch):
    from evolve.cli import main
    monkeypatch.chdir(tmp_path)
    (tmp_path / "status-run").mkdir()
    (tmp_path / "status-run" / "status.md").write_text("hello status\n")
    assert main(["status", "status-run"]) == 0
    assert "hello status" in capsys.readouterr().out

def _git(repo, *args):
    import subprocess
    return subprocess.run(["git", *args], cwd=repo, capture_output=True, text=True, check=True).stdout

def test_git_commits_carry_both_trailer_lines(tmp_path):
    _git(tmp_path, "init", "-q")
    _git(tmp_path, "config", "user.name", "t")
    _git(tmp_path, "config", "user.email", "t@example.com")
    _git(tmp_path, "commit", "-q", "--allow-empty", "-m", "init")
    c = cfg(generations=1, git={"enabled": True, "push": False})
    assert run(c, "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None) == EXIT_DONE
    msg = _git(tmp_path, "log", "-1", "--format=%B")
    assert msg.startswith("chore(run): t generation 1 best ")
    assert "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>" in msg
    assert "Claude-Session: https://claude.ai/code/session_01BUMdzXMSdYyesowPZnwehe" in msg

def test_git_nothing_to_commit_is_not_a_failure_and_still_pushes(tmp_path, monkeypatch):
    import subprocess
    from evolve.loop import _git as loop_git
    c = cfg(git={"enabled": True, "push": True})
    calls, logs = [], []
    def fake_run(cmd, **kw):
        calls.append(cmd[:2])
        if cmd[1] == "commit":
            return subprocess.CompletedProcess(cmd, 1, "nothing to commit, working tree clean\n", "")
        return subprocess.CompletedProcess(cmd, 0, "", "")
    monkeypatch.setattr("evolve.loop.subprocess.run", fake_run)
    (tmp_path / "runs" / "t").mkdir(parents=True)
    loop_git(c, tmp_path, logs.append, "msg")
    assert calls[-1] == ["git", "push"] and logs == []

def test_git_timeout_is_logged_not_raised(tmp_path, monkeypatch):
    import subprocess
    from evolve.loop import _git as loop_git
    seen, logs = {}, []
    def fake_run(cmd, **kw):
        seen.update(kw)
        raise subprocess.TimeoutExpired(cmd, kw["timeout"])
    monkeypatch.setattr("evolve.loop.subprocess.run", fake_run)
    (tmp_path / "runs" / "t").mkdir(parents=True)
    loop_git(cfg(git={"enabled": True, "push": True}), tmp_path, logs.append, "msg")
    assert seen["timeout"] == 120 and seen["env"]["GIT_TERMINAL_PROMPT"] == "0" and "timed out" in logs[0]


class SlowAbortable:
    """A mutator whose mutations take a moment; records abort()."""
    def __init__(self, delay=0.3):
        self.delay, self.aborted, self.started = delay, False, 0
        self.inner = FakeMutator(better, ok_smoke)

    def abort(self):
        self.aborted = True

    def mutate(self, task):
        import time
        self.started += 1
        if self.aborted:
            raise BudgetStop("aborted", calls=[{"cid": task.cid, "aborted": True}])
        time.sleep(self.delay)
        r = self.inner.mutate(task)
        r.calls = [{"cid": task.cid}]
        return r

def test_ctrl_c_drains_inflight_work_persists_it_and_reraises(tmp_path, monkeypatch):
    import evolve.loop as loop_mod
    real_wait, raised = loop_mod.wait, []
    def wait_once_interrupted(*a, **kw):
        if not raised:
            raised.append(1)
            raise KeyboardInterrupt
        return real_wait(*a, **kw)
    monkeypatch.setattr(loop_mod, "wait", wait_once_interrupted)
    m = SlowAbortable()
    c = cfg(generations=1, mutator={"kind": "fake", "concurrency": 2, "max_calls": 100})
    with pytest.raises(KeyboardInterrupt):
        run(c, "x", tmp_path, mutator=m, log=lambda *a: None)
    root = tmp_path / "runs" / "t"
    assert m.aborted and m.started == 2          # two were in flight; the third was never submitted
    plan = json.loads((root / "generations" / "001.plan.json").read_text())
    assert [t["status"] for t in plan["tasks"]] == ["made", "made", "pending"]
    assert (root / "candidates" / "g001-c00" / "program.py").exists()
    assert len((root / "calls.jsonl").read_text().splitlines()) == 2
    # resuming finishes the generation
    assert run(c, "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None) == EXIT_DONE

def test_ctrl_c_aborted_tasks_stay_pending_and_their_calls_are_logged(tmp_path, monkeypatch):
    import evolve.loop as loop_mod
    real_wait, raised = loop_mod.wait, []
    class AbortRaises(SlowAbortable):
        def mutate(self, task):
            import time
            self.started += 1
            time.sleep(self.delay)
            if self.aborted:
                raise BudgetStop("aborted", calls=[{"cid": task.cid, "aborted": True}])
            return self.inner.mutate(task)
    def wait_once_interrupted(*a, **kw):
        if not raised:
            raised.append(1)
            raise KeyboardInterrupt
        return real_wait(*a, **kw)
    monkeypatch.setattr(loop_mod, "wait", wait_once_interrupted)
    c = cfg(generations=1, mutator={"kind": "fake", "concurrency": 2, "max_calls": 100})
    with pytest.raises(KeyboardInterrupt):
        run(c, "x", tmp_path, mutator=AbortRaises(), log=lambda *a: None)
    root = tmp_path / "runs" / "t"
    plan = json.loads((root / "generations" / "001.plan.json").read_text())
    assert [t["status"] for t in plan["tasks"]] == ["pending"] * 3
    assert len((root / "calls.jsonl").read_text().splitlines()) == 2

def test_mutation_task_carries_zero_reasons_and_time_limit(tmp_path):
    from evolve.loop import _mutation_task
    from evolve.store import RunStore
    from tests.toy_problem import PROBLEM
    store = RunStore(tmp_path / "runs" / "t"); store.init("x")
    store.add_candidate("g000-seed", "def build(x, seed, time_limit):\n    return x\n",
                        {"id": "g000-seed", "generation": 0, "parents": [], "role": "seed"})
    store.write_result("g000-seed", {"cases": {
        "c1": {"case_id": "c1", "status": "ok", "valid": True, "value": 3.0, "score": 0.5, "reason": "", "wall_s": 0.1},
        "c2": {"case_id": "c2", "status": "timeout", "valid": False, "value": 0.0, "score": 0.0,
               "reason": "timeout: killed", "wall_s": 9.0}}, "fitness": 0.1})
    task = _mutation_task({"cid": "g001-c00", "role": "default", "parents": ["g000-seed"]}, store, PROBLEM, 7.5)
    _cid, _code, scores = task.parents[0]
    assert scores["c1"] == 3.0
    assert scores["c2"] == {"value": 0.0, "status": "timeout", "reason": "timeout: killed"}
    assert task.time_limit == 7.5

def test_progress_lines_and_gen_best(tmp_path):
    logs = []
    run(cfg(), "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=logs.append)
    assert "gen 1: made 3 failed 0 calls 0 gen-best 1.1222 best 1.1222" in logs
    assert "gen 2: made 3 failed 0 calls 0 gen-best 1.1222 best 1.1222" in logs
    rec = [l for l in logs if l.startswith("*** NEW RECORD")]
    assert rec == ["*** NEW RECORD c1: 7 > 6 (g001-c00) ***", "*** NEW RECORD c2: 11 > 10 (g001-c00) ***"]   # none repeated in gen 2
    root = tmp_path / "runs" / "t"
    s0 = json.loads((root / "generations" / "000.json").read_text())
    s1 = json.loads((root / "generations" / "001.json").read_text())
    assert s0["gen_best_fitness"] == pytest.approx(s0["best_fitness"])
    assert s1["gen_best_fitness"] == pytest.approx(1.1222, abs=1e-4) and s1["gen_best_fitness"] > s0["gen_best_fitness"]
    status = (root / "status.md").read_text()
    assert "| gen | made | failed | best fitness | gen best |" in status

def test_gen_best_is_per_generation_not_cumulative(tmp_path):
    weak = lambda t, a: "```python\ndef build(x, seed, time_limit):\n    return 1\n```"
    # generation 1 is good; generation 2 only echoes a weaker program
    replies = {1: better, 2: weak}
    class ByGen:
        def __init__(self): self.fakes = {g: FakeMutator(f, ok_smoke) for g, f in replies.items()}
        def mutate(self, task): return self.fakes[int(task.cid[1:4])].mutate(task)
    run(cfg(), "x", tmp_path, mutator=ByGen(), log=lambda *a: None)
    root = tmp_path / "runs" / "t"
    g1 = json.loads((root / "generations" / "001.json").read_text())
    g2 = json.loads((root / "generations" / "002.json").read_text())
    assert g2["best_fitness"] == g1["best_fitness"] and g2["gen_best_fitness"] < g2["best_fitness"]

def test_cli_passes_a_flushing_print(tmp_path, monkeypatch):
    import sys
    import evolve.cli as cli
    seen = {}
    monkeypatch.setattr(cli, "run", lambda cfg, text, root, **kw: seen.update(kw) or 0)
    monkeypatch.chdir(Path(__file__).parent.parent)
    assert cli.main(["run", "configs/smoke.toml", "--fake"]) == 0
    class Out:
        def __init__(self): self.w, self.flushes = [], 0
        def write(self, s): self.w.append(s)
        def flush(self): self.flushes += 1
    out = Out()
    monkeypatch.setattr(sys, "stdout", out)
    seen["log"]("hello")
    assert "hello" in "".join(out.w) and out.flushes >= 1

def _init_repo(path):
    _git(path, "init", "-q")
    _git(path, "config", "user.name", "t")
    _git(path, "config", "user.email", "t@example.com")
    _git(path, "commit", "-q", "--allow-empty", "-m", "init")

def test_git_commit_leaves_other_staged_files_alone(tmp_path):
    _init_repo(tmp_path)
    (tmp_path / "mine.txt").write_text("user's work")
    _git(tmp_path, "add", "mine.txt")
    c = cfg(generations=1, git={"enabled": True, "push": False})
    assert run(c, "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None) == EXIT_DONE
    for sha_range in ("HEAD", "HEAD~1"):
        assert "mine.txt" not in _git(tmp_path, "show", "--name-only", "--format=", sha_range)
    assert _git(tmp_path, "diff", "--cached", "--name-only").split() == ["mine.txt"]
    assert "runs/t/generations/001.json" in _git(tmp_path, "show", "--name-only", "--format=", "HEAD")

def test_git_second_commit_with_nothing_new_is_quiet(tmp_path):
    from evolve.loop import _git as loop_git
    _init_repo(tmp_path)
    (tmp_path / "runs" / "t").mkdir(parents=True)
    (tmp_path / "runs" / "t" / "f.txt").write_text("a")
    c, logs = cfg(git={"enabled": True, "push": False}), []
    loop_git(c, tmp_path, logs.append, "first")
    loop_git(c, tmp_path, logs.append, "second")
    assert logs == []
    assert _git(tmp_path, "log", "--format=%s").split("\n")[:2] == ["first", "init"]

def test_git_commit_is_scoped_to_run_paths(tmp_path, monkeypatch):
    import subprocess
    from evolve.loop import _git as loop_git
    (tmp_path / "runs" / "t").mkdir(parents=True)
    (tmp_path / "records").mkdir()
    cmds = []
    monkeypatch.setattr("evolve.loop.subprocess.run",
                        lambda cmd, **kw: cmds.append(cmd) or subprocess.CompletedProcess(cmd, 0, "", ""))
    loop_git(cfg(git={"enabled": True, "push": False}), tmp_path, lambda *_: None, "msg")
    commit = cmds[1]
    assert commit[:2] == ["git", "commit"] and commit[-3:] == ["--", "runs/t", "records"]
