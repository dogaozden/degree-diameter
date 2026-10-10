from evolve.types import load_problem
from tests.graphs import HEAWOOD, TUTTE_COXETER


def test_load_toy_problem():
    p = load_problem("tests.toy_problem")
    assert p.name == "toy" and [c.id for c in p.cases] == ["c1", "c2"]
    assert (p.harness_dir / "helper.py").exists() and p.seed_program.exists()


def test_known_graph_sizes():
    assert HEAWOOD[0] == 14 and len(HEAWOOD[1]) == 21
    assert TUTTE_COXETER[0] == 30 and len(TUTTE_COXETER[1]) == 45
