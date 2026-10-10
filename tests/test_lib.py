import itertools, random
import networkx as nx
import pytest
from problems.bipartite_dd import lib

def test_is_prime_power():
    assert [q for q in range(1, 30) if lib.is_prime_power(q)] == [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29]

@pytest.mark.parametrize("q", [2,3,4,5,7,8,9,16,25,27])
def test_field_axioms(q):
    F = lib.GF(q)
    els = range(q)
    for a in els:
        assert F.add(a, 0) == a and F.mul(a, 1) == a and F.add(a, F.neg(a)) == 0
        if a: assert F.mul(a, F.inv(a)) == 1
    rng = random.Random(q)
    for _ in range(300):
        a, b, c = (rng.randrange(q) for _ in range(3))
        assert F.mul(a, F.add(b, c)) == F.add(F.mul(a, b), F.mul(a, c))
        assert F.mul(F.mul(a, b), c) == F.mul(a, F.mul(b, c))
        assert F.add(a, b) == F.add(b, a) and F.mul(a, b) == F.mul(b, a)
    g = F.primitive_element()
    assert len({F.pow(g, e) for e in range(q - 1)}) == q - 1

def test_gf_rejects_non_prime_power():
    with pytest.raises(ValueError):
        lib.GF(6)

@pytest.mark.parametrize("q", [2,3,4,5,7,8,9,11])
def test_projective_plane_is_moore_graph(q):
    n, edges = lib.projective_plane_incidence(q)
    m = q*q + q + 1
    assert n == 2*m and len(edges) == (q+1)*m
    assert lib.max_degree(n, edges) == q + 1
    assert lib.is_bipartite(n, edges)
    assert lib.within_diameter(n, edges, 3)
    assert not lib.within_diameter(n, edges, 2)

def test_haar_heawood():
    n, edges = lib.haar_graph(7, [0, 1, 3])
    G = nx.Graph(edges)
    assert n == 14 and nx.is_bipartite(G) and nx.diameter(G) == 3
    assert {d for _, d in G.degree()} == {3}

def test_voltage_lift_matches_haar():
    n, edges = lib.voltage_lift(2, [(0, 1, 0), (0, 1, 1), (0, 1, 3)], 7)
    assert n == 14 and len(edges) == 21 and lib.within_diameter(n, edges, 3)

def test_voltage_lift_loop_dedup():
    n, edges = lib.voltage_lift(1, [(0, 0, 2)], 4)   # 2 == -2 mod 4: only 2 distinct edges
    assert n == 4 and sorted(edges) == [(0, 2), (1, 3)]

def test_within_diameter_matches_networkx():
    rng = random.Random(3)
    for _ in range(200):
        n = rng.randint(1, 12)
        edges = [(u, v) for u, v in itertools.combinations(range(n), 2) if rng.random() < 0.3]
        D = rng.randint(1, 4)
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
        expect = nx.is_connected(G) and (n == 1 or nx.diameter(G) <= D)
        assert lib.within_diameter(n, edges, D) == expect

def test_bad_pairs_path():
    assert lib.bad_pairs(4, [(0,1),(1,2),(2,3)], 2) == 1
    assert lib.bad_pairs(4, [(0,1),(1,2),(2,3)], 3) == 0
    assert lib.bad_pairs(3, [(0,1)], 5) == 2

def test_relabel():
    assert lib.relabel([(10, 30), (30, 20)]) == (3, [(0, 2), (2, 1)])
