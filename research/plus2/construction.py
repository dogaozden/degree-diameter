"""The +2 construction, coordinate-free: any projective plane of order q >= 4.

Input: a projective plane (points 0..N-1, lines as sets of points), an anti-flag (A, ell)
(A not on ell), a point P on ell, and four distinct points X0, X1, Xa, Xc on ell other than P.
Output: a bipartite graph of order 2(q^2+q+6), maximum degree q+2, diameter 3.

Notation: for a point X on ell, AX is the line through A and X; m_inf = AP.
New points: Q (clone of A), H_s (clone of X_s), s in {0,1,a,c}.
New lines:  M (clone of ell),   K_s (clone of AX_s).
"""
import random
import sys

import networkx as nx

sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[2]) + '/problems/bipartite_dd')
import lib


def pg_plane(q):
    """PG(2,q) from lib: (points list, lines list of frozensets)."""
    n, edges = lib.projective_plane_incidence(q)
    m = n // 2
    lines = [set() for _ in range(m)]
    for p, l in edges:
        lines[l - m].add(p)
    return list(range(m)), [frozenset(L) for L in lines]


def line_through(lines, x, y):
    for j, L in enumerate(lines):
        if x in L and y in L:
            return j
    raise ValueError('no line')


def core_incidences(points, lines, q, A, ell, P, X, hats=4):
    """Return (point names, line names, incidence set) of the core (no filler).

    X = [X0, X1, Xa, Xc] (points on ell).  hats=3 gives the Araujo-Pardo--Lopez core.
    """
    assert A not in lines[ell] and P in lines[ell]
    X0, X1, Xa, Xc = X
    assert len(set(X)) == 4 and all(x in lines[ell] and x != P for x in X)
    AX = {x: line_through(lines, A, x) for x in lines[ell]}
    minf = AX[P]
    inc = {(('p', p), ('l', j)) for j, L in enumerate(lines) for p in L}
    S = [X0, X1, Xa, Xc] if hats == 4 else [X0, X1, Xa]
    inc.remove((('p', Xa), ('l', AX[Xa])))
    rot = [X0, X1, Xc] if hats == 4 else [X0, X1]
    if hats == 4:
        # rotation: X1 on AX0, Xc on AX1, X0 on AXc instead of X_s on AX_s
        for x in rot:
            inc.remove((('p', x), ('l', AX[x])))
        for x, y in ((X1, X0), (Xc, X1), (X0, Xc)):
            inc.add((('p', x), ('l', AX[y])))
    pts = [('p', p) for p in points] + [('Q',)] + [('H', s) for s in S]
    lns = [('l', j) for j in range(len(lines))] + [('M',)] + [('K', s) for s in S]
    for s in S:
        for j, L in enumerate(lines):
            if s in L and j != ell:
                inc.add((('H', s), ('l', j)))          # H_s on every line through X_s but ell
        for p in lines[AX[s]]:
            if p != A:
                inc.add((('p', p), ('K', s)))          # K_s holds every point of AX_s but A
    off_M = set(rot)                                   # points of ell not on M
    for x in lines[ell]:
        if x not in off_M:
            inc.add((('p', x), ('M',)))                # M holds P and the rest of ell ...
    for s in S:
        inc.add((('H', s), ('M',)))                    # ... and all hat points
    for x in lines[ell]:
        if x not in off_M:
            inc.add((('Q',), ('l', AX[x])))            # Q on m_inf and the matching lines AX
    for s in S:
        inc.add((('Q',), ('K', s)))
    inc.add((('p', A), ('K', Xa)))
    inc.add((('H', Xa), ('l', ell)))
    if hats == 4:
        inc.add((('H', X0), ('K', Xc)))
        inc.add((('H', Xc), ('K', X1)))
        inc.add((('H', X1), ('K', X0)))
    else:
        inc.add((('H', X0), ('K', X1)))
        inc.add((('H', X1), ('K', X0)))
    return pts, lns, inc


def to_graph(pts, lns, inc):
    ids = {v: i for i, v in enumerate(pts + lns)}
    return len(ids), sorted((ids[a], ids[b]) for a, b in inc), ids


def fill(n, edges, d, ids_side):
    """Add a maximum matching between points and lines of degree < d that are not yet adjacent."""
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1; deg[v] += 1; adj[u].add(v); adj[v].add(u)
    pts = [u for u in range(n) if ids_side[u] == 0 and deg[u] < d]
    lns = [v for v in range(n) if ids_side[v] == 1 and deg[v] < d]
    G = nx.Graph()
    G.add_nodes_from(pts); G.add_nodes_from(lns)
    G.add_edges_from((u, v) for u in pts for v in lns if v not in adj[u])
    M = nx.bipartite.maximum_matching(G, top_nodes=pts) if pts else {}
    extra = [(u, M[u]) for u in pts if u in M]
    return sorted(edges + extra)


def build(points, lines, q, A, ell, P, X, hats=4, regular=True):
    pts, lns, inc = core_incidences(points, lines, q, A, ell, P, X, hats)
    n, edges, ids = to_graph(pts, lns, inc)
    if regular:
        side = [0] * len(pts) + [1] * len(lns)
        edges = fill(n, edges, q + 2, side)
    return n, edges


def default_frame(points, lines, rng=None):
    """A, ell, P, X0..Xc: fixed (first choices) or random if rng is given."""
    pick = (lambda s: rng.choice(sorted(s))) if rng else (lambda s: min(s))
    ell = rng.randrange(len(lines)) if rng else 0
    A = pick(set(points) - lines[ell])
    on = sorted(lines[ell])
    if rng:
        rng.shuffle(on)
    P, X = on[0], on[1:5]
    return A, ell, P, X


if __name__ == '__main__':
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for q in range(2, 17):
        if not lib.is_prime_power(q):
            continue
        if q < 4:
            print(f'q={q}: needs 4 points on ell besides P, impossible for q<4')
            continue
        points, lines = pg_plane(q)
        rng = random.Random(q)
        res = []
        for t in range(trials):
            A, ell, P, X = default_frame(points, lines, rng if t else None)
            n, e = build(points, lines, q, A, ell, P, X)
            res.append((n, lib.max_degree(n, e), lib.is_valid(n, e, q + 2, 3)))
        print(f'q={q}: d={q+2}', res)
