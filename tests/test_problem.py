import pytest
from evolve.types import CheckerBug, Case
from problems.bipartite_dd.problem import PROBLEM
from tests.graphs import HEAWOOD

def test_cases_loaded():
    ids = [c.id for c in PROBLEM.cases]
    assert ids[:3] == ["d3D3", "d4D3", "d5D3"] and len(ids) == 13
    c = {c.id: c for c in PROBLEM.cases}
    assert c["d4D5"].record == 160 and c["d4D5"].ceiling == 236 and c["d4D5"].kind == "target" and c["d4D5"].weight == 2
    assert c["d7D3"].params == {"d": 7, "D": 3}

def test_evaluate_and_verify():
    c = PROBLEM.smoke_case()
    assert c.id == "d3D3"
    assert PROBLEM.evaluate(c, HEAWOOD) == (True, 14.0, "")
    assert PROBLEM.verify(c, HEAWOOD)
    ok, value, reason = PROBLEM.evaluate(c, (3, [(0, 1), (1, 2), (2, 0)]))
    assert not ok and value == 0.0 and reason.startswith("not bipartite")

def test_ceiling_breach_raises():
    low = Case("x", {"d": 3, "D": 3}, record=10, ceiling=10, kind="target", weight=1)
    with pytest.raises(CheckerBug):
        PROBLEM.evaluate(low, HEAWOOD)

def test_prompt_context_mentions_interface_and_lib():
    t = PROBLEM.prompt_context()
    assert "def build(d, D, seed, time_limit)" in t and "def voltage_lift" in t and "Voltage lifts" in t

def test_seed_valid_everywhere_and_optimal_on_planes():
    import importlib.util, sys
    sys.path.insert(0, str(PROBLEM.harness_dir))
    spec = importlib.util.spec_from_file_location("seed_mod", PROBLEM.seed_program)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    for c in PROBLEM.cases:
        out = mod.build(**c.params, seed=0, time_limit=2.0)
        ok, value, reason = PROBLEM.evaluate(c, out)
        assert ok, (c.id, reason)
        if c.id in ("d3D3", "d4D3", "d5D3", "d6D3"):
            assert value == c.record
