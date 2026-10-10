import random
import pytest
from evolve.store import RunStore, CandidateRecord
from evolve.select import fitness, parent_pool, pick_roles, pick_parents
from evolve.types import Case

CASES = [Case("a", {}, 10, 20, "calibration", 1), Case("b", {}, 10, 20, "target", 2)]

def res(va, vb):
    return {"cases": {"a": {"status": "ok", "valid": True, "value": va, "score": va/10, "reason": "", "wall_s": 0.1},
                      "b": {"status": "ok", "valid": True, "value": vb, "score": vb/10, "reason": "", "wall_s": 0.1}},
            "fitness": fitness({"a": va/10, "b": vb/10}, CASES)}

def test_fitness_weighted():
    assert fitness({"a": 1.0, "b": 0.5}, CASES) == pytest.approx((1.0 + 2*0.5) / 3)
    assert fitness({"a": 1.0}, CASES) == pytest.approx(1/3)

def test_store_roundtrip(tmp_path):
    s = RunStore(tmp_path / "run"); s.init("x = 1\n"); s.init("ignored")
    assert (s.root / "config.toml").read_text() == "x = 1\n"
    s.add_candidate("g000-seed", "def build(): pass\n", {"id": "g000-seed", "generation": 0, "parents": [], "role": "seed", "mutator": {}})
    with pytest.raises(FileExistsError):
        s.add_candidate("g000-seed", "", {})
    assert s.read_program("g000-seed").startswith("def build")
    assert not s.has_result("g000-seed")
    s.write_result("g000-seed", res(10, 5))
    [c] = s.load_candidates()
    assert c.fitness == pytest.approx((1 + 2*0.5)/3) and c.case_values == {"a": 10, "b": 5}
    assert s.candidates_in_generation(0) == ["g000-seed"] and s.candidates_in_generation(1) == []
    assert not s.generation_done(0)
    s.write_generation(0, {"complete": False}); assert not s.generation_done(0)
    s.write_generation(0, {"complete": True}); assert s.generation_done(0)
    s.append_call({"a": 1}); s.append_call({"a": 2}); assert s.count_calls() == 2
    s.write_plan(1, {"tasks": []}); assert s.read_plan(1) == {"tasks": []} and s.read_plan(2) is None

def rec(cid, g, fit, va, vb):
    return CandidateRecord(cid, g, [], "default", fit, {"a": va, "b": vb}, {"a": va/10, "b": vb/10})

def test_parent_pool_keeps_specialist():
    cands = [rec("g001-c00", 1, 0.9, 10, 10), rec("g001-c01", 1, 0.8, 9, 10), rec("g001-c02", 1, 0.2, 0, 12),
             rec("g001-c03", 1, 0.0, 0, 0), CandidateRecord("g001-c04", 1, [], "x", None, {}, {})]
    pool = parent_pool(cands, CASES, elite_k=2)
    assert pool == ["g001-c00", "g001-c01", "g001-c02"]

def test_sampling_deterministic():
    w = {"default": 0.5, "crossover": 0.2, "invent": 0.15, "moonshot": 0.15}
    assert pick_roles(8, w, random.Random(1)) == pick_roles(8, w, random.Random(1))
    assert len(pick_parents(["x", "y", "z"], "crossover", random.Random(2))) == 2
    assert pick_parents(["x"], "crossover", random.Random(2)) == ["x"]
    assert len(pick_parents(["x", "y"], "default", random.Random(2))) == 1
