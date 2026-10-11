import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / structured constructions kept as safe baselines.
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
# New construction: random bipartite d-regular graphs grown by a
# "pair insertion" operator and repaired by simulated annealing over
# 2-switches, with the cost = number of ordered vertex pairs at distance > D.
#
# State: NA (h x d), NB (h x d). A-vertex i has B-neighbours NA[i];
# B-vertex j has A-neighbours NB[j]. Unified labels: A i -> i, B j -> h + j.
#
# Growth (one pair): choose d A-vertices x_k with neighbours y_k, replace
# edge x_k y_k by x_k b* and a* y_k, where a*, b* are new. Stays d-regular
# and simple; it is always the start of a repair phase.
#
# Repair: 2-switches (a1 b1, a2 b2 -> a1 b2, a2 b1) that keep the graph
# simple and bipartite. Moves are biased toward vertices with unreached pairs.
# ----------------------------------------------------------------------------

_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _eval(NA, NB, h, d, D):
    """Return (cost, deficit): cost = ordered pairs at distance > D; deficit[v] = unreached count of v."""
    U = np.concatenate((NA + h, NB), axis=0)
    N = 2 * h
    W = (N + 63) // 64
    r = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N, dtype=np.int64)
    r[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = r.copy()
        for l in range(d):
            new |= r[U[:, l]]
        if np.array_equal(new, r):
            break
        r = new
    pc = _POP16[r.view(np.uint16)].sum(axis=1)
    cost = N * N - int(pc.sum())
    deficit = N - pc
    return cost, deficit


def _switch(NA, NB, E, h, a1, p, a2, q):
    """Apply the 2-switch (a1 p, a2 q). Unchecked; the same call with the same indices undoes it."""
    b1 = int(NA[a1, p])
    b2 = int(NA[a2, q])
    NA[a1, p] = b2
    NA[a2, q] = b1
    i = int(np.flatnonzero(NB[b1] == a1)[0])
    NB[b1, i] = a2
    i = int(np.flatnonzero(NB[b2] == a2)[0])
    NB[b2, i] = a1
    E.discard(a1 * h + b1)
    E.discard(a2 * h + b2)
    E.add(a1 * h + b2)
    E.add(a2 * h + b1)


def _anneal(NA, NB, h, d, D, rng, t_end):
    """Repair by annealing until cost 0 or time t_end. Returns (ok, NA, NB)."""
    NA = NA.copy()
    NB = NB.copy()
    E = set(a * h + int(b) for a in range(h) for b in NA[a])
    cost, deficit = _eval(NA, NB, h, d, D)
    t_start = time.monotonic()
    span = max(1e-3, t_end - t_start)
    T0 = max(2.0, 0.05 * cost)
    T1 = 0.5
    while cost > 0:
        now = time.monotonic()
        if now >= t_end:
            return False, None, None
        frac = (now - t_start) / span
        T = T0 * (T1 / T0) ** frac

        bad = np.flatnonzero(deficit > 0)
        if bad.size and rng.random() < 0.5:
            v = int(bad[rng.randrange(bad.size)])
            if v < h:
                a1 = v
            else:
                a1 = int(NB[v - h, rng.randrange(d)])
        else:
            a1 = rng.randrange(h)
        p = rng.randrange(d)
        a2 = rng.randrange(h)
        if a2 == a1:
            continue
        q = rng.randrange(d)
        b1 = int(NA[a1, p])
        b2 = int(NA[a2, q])
        if b1 == b2:
            continue
        if (a1 * h + b2) in E or (a2 * h + b1) in E:
            continue

        _switch(NA, NB, E, h, a1, p, a2, q)
        c2, def2 = _eval(NA, NB, h, d, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost, deficit = c2, def2
        else:
            _switch(NA, NB, E, h, a1, p, a2, q)  # undo
    return True, NA, NB


def _grow1(NA, NB, h, d, rng):
    """Insert one A-vertex and one B-vertex, keeping d-regularity and simplicity."""
    NA = NA.copy()
    NB = NB.copy()
    while True:
        xs = rng.sample(range(h), d)
        ys = [int(NA[x, rng.randrange(d)]) for x in xs]
        if len(set(ys)) == d:
            break
    for x, y in zip(xs, ys):
        j = int(np.flatnonzero(NA[x] == y)[0])
        NA[x, j] = h          # x now adjacent to new B-vertex h
        i = int(np.flatnonzero(NB[y] == x)[0])
        NB[y, i] = h          # y now adjacent to new A-vertex h
    newA = np.array(ys, dtype=np.int64)[None, :]
    newB = np.array(xs, dtype=np.int64)[None, :]
    NA = np.vstack([NA, newA])
    NB = np.vstack([NB, newB])
    return NA, NB, h + 1


def _to_edges(NA, NB, h):
    edges = []
    for a in range(h):
        for b in NA[a]:
            edges.append((a, h + int(b)))
    return 2 * h, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
        return best
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return best

    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: grow a d-regular bipartite graph and repair its diameter.
    NA = np.array([list(range(d)) for _ in range(d)], dtype=np.int64)
    NB = NA.copy()
    h = d
    step = max(1, h // 20)

    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining <= 0.05:
            break
        cNA, cNB, ch = NA, NB, h
        for _ in range(step):
            cNA, cNB, ch = _grow1(cNA, cNB, ch, d, rng)
        slice_len = min(remaining, max(2.0, remaining / 4.0))
        ok, aNA, aNB = _anneal(cNA, cNB, ch, d, D, rng,
                               time.monotonic() + slice_len)
        if ok:
            NA, NB, h = aNA, aNB, ch
            n, e = _to_edges(NA, NB, h)
            consider(n, e)
            step = min(step * 2, max(1, h // 10))
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
