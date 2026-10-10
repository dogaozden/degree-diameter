import random
import pytest
from problems.bipartite_dd.checker import check, parse_output
from problems.bipartite_dd.checker_nx import check_nx
from tests.graphs import HEAWOOD, TUTTE_COXETER, lcf

BOTH = [check, check_nx]

@pytest.mark.parametrize("fn", BOTH)
def test_heawood_valid(fn):
    r = fn(HEAWOOD, 3, 3)
    assert r.valid and r.n == 14 and r.reason == ""

@pytest.mark.parametrize("fn", BOTH)
def test_tutte_coxeter_valid_d3D4_not_D3(fn):
    assert fn(TUTTE_COXETER, 3, 4).valid
    r = fn(TUTTE_COXETER, 3, 3)
    assert not r.valid and r.reason.startswith("diameter")

@pytest.mark.parametrize("fn", BOTH)
def test_k4_not_bipartite(fn):
    edges = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
    r = fn((4, edges), 3, 3)
    assert not r.valid and r.reason.startswith("not bipartite")

@pytest.mark.parametrize("fn", BOTH)
def test_degree_violation(fn):
    star = (5, [(0,1),(0,2),(0,3),(0,4)])
    r = fn(star, 3, 3)
    assert not r.valid and r.reason.startswith("degree")

@pytest.mark.parametrize("fn", BOTH)
def test_cycle16_too_wide(fn):
    c16 = (16, [(i, (i+1) % 16) for i in range(16)])
    r = fn(c16, 3, 3)
    assert not r.valid and r.reason.startswith("diameter")
    assert fn(c16, 2, 8).valid

@pytest.mark.parametrize("fn", BOTH)
def test_duplicate_and_selfloop(fn):
    assert fn((2, [(0,1),(1,0)]), 3, 3).reason.startswith("duplicate edge")
    assert fn((2, [(0,0),(0,1)]), 3, 3).reason.startswith("self-loop")

@pytest.mark.parametrize("fn", BOTH)
def test_disconnected_fails(fn):
    n, e = HEAWOOD
    two = (2*n, e + [(u+n, v+n) for u, v in e])
    r = fn(two, 3, 3)
    assert not r.valid and r.reason.startswith("diameter")
    isolated = (15, list(e))
    assert fn(isolated, 3, 3).reason.startswith("diameter")

@pytest.mark.parametrize("fn", BOTH)
@pytest.mark.parametrize("bad", ["x", None, [3], (True, []), (3, [(0,)]), (3, [(0, 5)]), (3, [(0, 1.0)]), {"n": 2}, (0, [])])
def test_malformed(fn, bad):
    r = fn(bad, 3, 3)
    assert not r.valid
    assert r.reason.startswith("malformed") or r.reason.startswith("label out of range")

def test_parse_accepts_tuple_and_dict():
    assert parse_output([2, [[0, 1]]]) == (2, [(0, 1)])
    assert parse_output({"n": 2, "edges": [(0, 1)]}) == (2, [(0, 1)])

@pytest.mark.parametrize("fn", BOTH)
def test_single_vertex_valid(fn):
    assert fn((1, []), 3, 3).valid

def test_checkers_agree_on_random_graphs():
    rng = random.Random(7)
    for _ in range(300):
        a = rng.randint(1, 9); b = rng.randint(1, 9); n = a + b
        p = rng.random()
        edges = [(i, a + j) for i in range(a) for j in range(b) if rng.random() < p]
        if rng.random() < 0.2 and n >= 3:
            edges.append((0, 1 if a > 1 else n - 1))  # sometimes break bipartiteness
        edges = list(dict.fromkeys(tuple(sorted(e)) for e in edges if e[0] != e[1]))
        d = rng.randint(1, 6); D = rng.randint(1, 5)
        assert check((n, edges), d, D).valid == check_nx((n, edges), d, D).valid
