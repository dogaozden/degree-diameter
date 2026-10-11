import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / structured baselines (kept as safe fallbacks and calibration returns).
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
# New construction: random bipartite d-regular-ish graphs (d permutations
# between two sides of size N) repaired by annealed layer swaps, with the
# cost being the number of unreached (vertex, vertex) pairs within distance D.
# No group structure is imposed, unlike the bi-Cayley lifts.
#
# Vertices: A_i = i (i < N), B_j = N + j.
# Layer l is a permutation sig[l]: A_i ~ B_{sig[l][i]}.
# A swap of two A-partners within one layer keeps every layer a permutation,
# so the maximum degree stays d. Duplicate edges are merged at output time;
# that only lowers degrees and never changes reachability.
# ----------------------------------------------------------------------------

_TBL = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_HAS_BC = hasattr(np, "bitwise_count")


def _ball_deficit(nb, n, D):
    """Per-vertex count of vertices NOT within distance D (bit-packed BFS over all sources)."""
    d = nb.shape[0]
    W = (n + 63) // 64
    idx = np.arange(n)
    reach = np.zeros((n, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nb[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    if _HAS_BC:
        cnt = np.bitwise_count(reach).sum(axis=1, dtype=np.int64)
    else:
        cnt = _TBL[reach.view(np.uint8)].sum(axis=1)
    return n - cnt


def _swap(sig, inv, nb, N, l, i1, i2):
    """Exchange the B-partners of A-vertices i1 and i2 in layer l. Applying it twice is the identity."""
    a = sig[l, i1]
    b = sig[l, i2]
    sig[l, i1] = b
    sig[l, i2] = a
    inv[l, a] = i2
    inv[l, b] = i1
    nb[l, i1] = N + b
    nb[l, i2] = N + a
    nb[l, N + a] = i2
    nb[l, N + b] = i1


def _anneal(d, D, N, deadline, rng):
    """Anneal layer swaps until every pair is within distance D. Returns nb (d, 2N) or None."""
    gen = np.random.default_rng(rng.randrange(1 << 31))
    n = 2 * N
    sig = np.stack([gen.permutation(N) for _ in range(d)]).astype(np.int64)
    inv = np.argsort(sig, axis=1).astype(np.int64)
    nb = np.empty((d, n), dtype=np.int64)
    nb[:, :N] = N + sig
    nb[:, N:] = inv

    deficit = _ball_deficit(nb, n, D)
    cost = int(deficit.sum())
    if cost == 0:
        return nb

    T0, T1 = 5.0, 0.3
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        temp = T0 * (T1 / T0) ** frac

        l = rng.randrange(d)
        if rng.random() < 0.6:
            # Targeted: rewire a vertex that still misses some vertex.
            cand = np.flatnonzero(deficit)
            v = int(cand[rng.randrange(cand.size)])
            i1 = v if v < N else int(inv[l, v - N])
        else:
            i1 = rng.randrange(N)
        i2 = rng.randrange(N)
        if i2 == i1:
            continue

        _swap(sig, inv, nb, N, l, i1, i2)
        nd = _ball_deficit(nb, n, D)
        c2 = int(nd.sum())
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            deficit = nd
        else:
            _swap(sig, inv, nb, N, l, i1, i2)
    return nb


def _edges(nb, N):
    es = set()
    for l in range(nb.shape[0]):
        for i in range(N):
            es.add((i, int(nb[l, i])))
    return sorted(es)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    if D == 2:
        return best

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

    # Random bipartite search with bisection on the side size N.
    max_N = max(2, lib.moore_bound(d, D) // 2)
    lo = 0          # largest N known to succeed
    hi = None       # smallest N known to fail
    N = max(2, best_n // 2 + 1)

    while time.monotonic() < deadline - 0.5:
        if N > max_N:
            N = max_N
        if hi is not None and hi - lo <= 1:
            break
        remaining = deadline - time.monotonic()
        slice_end = time.monotonic() + min(remaining, max(3.0, 0.4 * remaining))
        nb = _anneal(d, D, N, slice_end, rng)

        if nb is not None:
            consider(2 * N, _edges(nb, N))
            lo = max(lo, N)
            if hi is None:
                N = int(lo * 1.08) + 1
            else:
                N = (lo + hi) // 2
        else:
            hi = N if hi is None else min(hi, N)
            if lo == 0:
                N = max(2, N // 2)
                if N <= 2 and hi <= 2:
                    break
            else:
                if hi - lo <= 1:
                    break
                N = (lo + hi) // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
