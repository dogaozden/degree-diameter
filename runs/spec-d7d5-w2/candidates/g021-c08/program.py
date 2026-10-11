import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions (kept for calibration-style cases D = 3, 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: random d-regular bipartite graphs with local search.
#
# A d-regular bipartite graph on h + h vertices is kept as two list-of-lists:
# nbA[a] = B-neighbours of A-vertex a, nbB[b] = A-neighbours of B-vertex b.
# Moves are double-edge switches (a1-b1, a2-b2) -> (a1-b2, a2-b1), which keep
# every degree equal to d and the graph simple. The cost is the number of
# ordered vertex pairs at distance > D, computed with packed uint64 bitsets.
# Simulated annealing drives the cost to zero. Growth adds one pair of vertices
# at a time (x on side A, y on side B, x~y, and d-1 removed edges re-attached),
# then re-anneals. Every step keeps all degrees equal to d.
# Each accepted graph is checked by lib.is_valid before it is returned.
# ----------------------------------------------------------------------------

_P8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _cost(nbA, nbB, h, d, D):
    """Number of ordered pairs at distance > D in the graph with parts of size h."""
    n = 2 * h
    nb = np.empty((n, d), dtype=np.int64)
    nb[:h] = np.array(nbA, dtype=np.int64) + h
    nb[h:] = np.array(nbB, dtype=np.int64)
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for j in range(d):
            new |= reach[nb[:, j]]
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_P8[reach.view(np.uint8)].sum())
    return n * n - total


def _switch(nbA, nbB, h, d, rng):
    """Random double-edge switch. Returns an undo record, or None if the proposal is invalid."""
    a1 = rng.randrange(h)
    a2 = rng.randrange(h)
    if a1 == a2:
        return None
    s1 = rng.randrange(d)
    s2 = rng.randrange(d)
    b1 = nbA[a1][s1]
    b2 = nbA[a2][s2]
    if b1 == b2 or b2 in nbA[a1] or b1 in nbA[a2]:
        return None
    i1 = nbB[b1].index(a1)
    i2 = nbB[b2].index(a2)
    nbA[a1][s1] = b2
    nbA[a2][s2] = b1
    nbB[b1][i1] = a2
    nbB[b2][i2] = a1
    return (a1, s1, a2, s2, b1, b2, i1, i2)


def _unswitch(nbA, nbB, u):
    a1, s1, a2, s2, b1, b2, i1, i2 = u
    nbA[a1][s1] = b1
    nbA[a2][s2] = b2
    nbB[b1][i1] = a1
    nbB[b2][i2] = a2


def _anneal(nbA, nbB, h, d, D, rng, deadline):
    """Anneal with double-edge switches until the cost is zero. Returns True on success."""
    cost = _cost(nbA, nbB, h, d, D)
    if cost == 0:
        return True
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = max(1.0, 0.02 * cost)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        T = max(0.05, T0 * (1.0 - (now - t0) / span))
        u = _switch(nbA, nbB, h, d, rng)
        if u is None:
            continue
        new = _cost(nbA, nbB, h, d, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            _unswitch(nbA, nbB, u)
    return True


def _insert(nbA, nbB, h, d, rng):
    """Add one A-vertex x (index h) and one B-vertex y (index h). Returns the new h, or None."""
    chosen = []
    usedA, usedB = set(), set()
    for _ in range(50 * d * d):
        if len(chosen) == d - 1:
            break
        a = rng.randrange(h)
        b = nbA[a][rng.randrange(d)]
        if a in usedA or b in usedB:
            continue
        chosen.append((a, b))
        usedA.add(a)
        usedB.add(b)
    if len(chosen) < d - 1:
        return None
    x = h
    y = h
    for a, b in chosen:
        nbA[a][nbA[a].index(b)] = y
        nbB[b][nbB[b].index(a)] = x
    nbA.append([b for _, b in chosen] + [y])
    nbB.append([a for a, _ in chosen] + [x])
    return h + 1


def _grow(d, D, rng, deadline):
    """Find a valid d-regular bipartite graph with diameter <= D and grow it as far as time allows."""
    if d < 3:
        return None
    H0 = max(d + 1, int(0.36 * lib.moore_bound(d, D) / 2))
    h = H0
    cur = None
    while time.monotonic() < deadline and cur is None:
        nbA = [[(a + j) % h for j in range(d)] for a in range(h)]
        nbB = [[(b - j) % h for j in range(d)] for b in range(h)]
        for _ in range(4 * h * d):
            _switch(nbA, nbB, h, d, rng)
        if _anneal(nbA, nbB, h, d, D, rng, min(deadline, time.monotonic() + 10.0)):
            cur = (h, nbA, nbB)
        else:
            h = max(d + 1, int(h * 0.98))
    if cur is None:
        return None

    h, A, B = cur
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        nA = [row[:] for row in A]
        nB = [row[:] for row in B]
        h2 = _insert(nA, nB, h, d, rng)
        if h2 is None:
            break
        step_end = min(deadline, time.monotonic() + 8.0)
        if _anneal(nA, nB, h2, d, D, rng, step_end):
            h, A, B = h2, nA, nB
            fails = 0
        else:
            fails += 1
    return h, A, B


def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Use about 85% of the limit, keeping a safety margin for verification and output.
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # New construction: local search on random regular bipartite graphs.
    if d >= 3 and D >= 3 and time.monotonic() < deadline:
        try:
            res = _grow(d, D, rng, deadline)
            if res is not None:
                h, A, B = res
                edges = [(a, h + b) for a in range(h) for b in A[a]]
                consider(2 * h, edges)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
