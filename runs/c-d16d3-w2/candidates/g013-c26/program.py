"""Arc-extended PG(2,q) base plus an annealed repair search that grows the graph one vertex at a time.

Base: incidence graph of PG(2,q), q the largest prime power with q+1 <= d, extended by
pencil-type A-vertices and dual B-vertices using the spare degree s = d-q-1 (conic or greedy arc).

Growth: append one vertex on a side with spare degree, then anneal degree-preserving edge
swaps and spare-degree additions, with cost = number of vertex pairs at distance > D (computed
from boolean powers of I+A with numpy). Each accepted size is recorded only after exact
validation with lib.is_valid, and the best valid graph is always returned.
"""
import math
import random
import time

import numpy as np

import lib


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _base(d, rng, deadline):
    """Return (n, edges, side) for the arc-extended PG(2,q) graph, or None if no prime power fits."""
    q = None
    for qq in range(d - 1, 1, -1):
        if lib.is_prime_power(qq):
            q = qq
            break
    if q is None:
        return None
    n2, inc = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in inc:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    s = d - q - 1
    S = []
    if s >= 1:
        S = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
    if s >= 2:
        F = lib.GF(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            cs.append(index[(0, 1, 0)])
        if len(cs) > len(S) and _loads_ok(cs, s, m, point_lines, line_points):
            S = cs
    if not _loads_ok(S, s, m, point_lines, line_points):
        S = []

    edges = list(inc)
    side = [0] * m + [1] * m
    n = 2 * m
    for P in S:  # A-vertex on the point side, joined to the pencil of P
        x = n
        n += 1
        side.append(0)
        for L in point_lines[P]:
            edges.append((x, m + L))
    for j in S:  # B-vertex on the line side, joined to the points of line j
        y = n
        n += 1
        side.append(1)
        for Q in line_points[j]:
            edges.append((Q, y))
    return n, edges, side


# ----------------------------------------------------------------------------
# Repair search: grow the graph one vertex at a time.
# ----------------------------------------------------------------------------

def _cost(A, n, D):
    """Number of unordered vertex pairs at distance > D (zero means diameter <= D)."""
    R = A.copy()
    np.fill_diagonal(R, 1.0)
    P = R
    for _ in range(D - 1):
        P = ((P @ R) > 0).astype(np.float32)
    reached = int(np.count_nonzero(P))
    return (n * n - reached) // 2


def _apply(nb, A, ops, add, u, v):
    if add:
        nb[u].add(v)
        nb[v].add(u)
        A[u, v] = 1.0
        A[v, u] = 1.0
    else:
        nb[u].discard(v)
        nb[v].discard(u)
        A[u, v] = 0.0
        A[v, u] = 0.0
    ops.append((add, u, v))


def _undo(nb, A, ops):
    for add, u, v in reversed(ops):
        if add:
            nb[u].discard(v)
            nb[v].discard(u)
            A[u, v] = 0.0
            A[v, u] = 0.0
        else:
            nb[u].add(v)
            nb[v].add(u)
            A[u, v] = 1.0
            A[v, u] = 1.0


def _move(nb, A, side, n, d, rng, ops):
    """Propose one local change (recorded in ops). Returns False if nothing was applied."""
    s0 = [v for v in range(n) if side[v] == 0]
    s1 = [v for v in range(n) if side[v] == 1]
    r = rng.random()
    if r < 0.35:  # add an edge between two spare-degree vertices on opposite sides
        sp0 = [v for v in s0 if len(nb[v]) < d]
        sp1 = [v for v in s1 if len(nb[v]) < d]
        if not sp0 or not sp1:
            return False
        for _ in range(12):
            a = rng.choice(sp0)
            b = rng.choice(sp1)
            if b not in nb[a]:
                _apply(nb, A, ops, True, a, b)
                return True
        return False
    a = rng.choice(s0)
    if not nb[a]:
        return False
    if r < 0.8:  # degree-preserving double edge swap
        c = rng.choice(s0)
        if c == a or not nb[c]:
            return False
        b = rng.choice(tuple(nb[a]))
        e = rng.choice(tuple(nb[c]))
        if e in nb[a] or b in nb[c]:
            return False
        _apply(nb, A, ops, False, a, b)
        _apply(nb, A, ops, False, c, e)
        _apply(nb, A, ops, True, a, e)
        _apply(nb, A, ops, True, c, b)
        return True
    # move one endpoint of an edge to a spare-degree vertex
    b = rng.choice(tuple(nb[a]))
    sp1 = [v for v in s1 if len(nb[v]) < d and v not in nb[a] and v != b]
    if not sp1:
        return False
    e = rng.choice(sp1)
    _apply(nb, A, ops, False, a, b)
    _apply(nb, A, ops, True, a, e)
    return True


def _grow(n, edges, side, d, D, deadline, rng):
    """Repeatedly append a vertex and anneal until cost 0; return the largest valid (n, edges) reached."""
    nb = [set() for _ in range(n)]
    for u, v in edges:
        nb[u].add(v)
        nb[v].add(u)
    A = np.zeros((n, n), dtype=np.float32)
    for u, v in edges:
        A[u, v] = 1.0
        A[v, u] = 1.0
    best_n, best_edges = n, list(edges)
    while time.monotonic() < deadline:
        spare = {0: any(len(nb[v]) < d for v in range(n) if side[v] == 0),
                 1: any(len(nb[v]) < d for v in range(n) if side[v] == 1)}
        cs = [c for c in (0, 1) if spare[1 - c]]
        if not cs:
            break
        c = rng.choice(cs)
        nb.append(set())
        side.append(c)
        n += 1
        A = np.pad(A, ((0, 1), (0, 1)))
        cur = _cost(A, n, D)
        ok = cur == 0
        steps = 0
        while not ok and time.monotonic() < deadline:
            steps += 1
            T = 0.6 * max(0.03, 1.0 - steps / 4000.0)
            ops = []
            if not _move(nb, A, side, n, d, rng, ops):
                continue
            new = _cost(A, n, D)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
                ok = cur == 0
            else:
                _undo(nb, A, ops)
        if not ok:
            break
        best_n = n
        best_edges = [(u, v) for u in range(n) for v in nb[u] if u < v]
    return best_n, best_edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        try:
            base = _base(d, rng, start + 0.1 * time_limit)
        except Exception:
            base = None
        if base is not None:
            n, e, side = base
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            if time.monotonic() < deadline and lib.is_valid(n, e, d, D):
                try:
                    n2, e2 = _grow(n, e, side, d, D, deadline, rng)
                    if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                        best = (n2, e2)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
