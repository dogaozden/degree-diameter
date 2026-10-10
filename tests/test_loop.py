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
