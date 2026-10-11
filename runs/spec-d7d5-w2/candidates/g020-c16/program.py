import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged from the parent): PG(2,q) for D = 3, W(q) for D = 4.
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
# NEW routine: bit-packed whole-graph reach with 2-switch annealing.
#
# The graph is a union of d random perfect matchings between h "A" and h "B"
# vertices (a d-regular bipartite multigraph). Moves swap the B-targets of two
# A-vertices in one matching layer. This is a 2-switch: degrees and
# bipartiteness are preserved and only the wiring changes.
#
# Cost = (# unordered pairs at distance > D) + PEN * (# duplicate edges).
# Reach sets are packed 64 vertices per uint64 word, so one full evaluation is
# D rounds of d gathers of an (N, N/64) array, which is cheap at N ~ 1200.
# Random regular bipartite graphs of this order are already close to diameter
# D, so annealing from random wiring can reach orders above the structured
# records for the target case.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PEN = 30


def _reach_bits(nbr, N, D):
    """Packed reach sets: bit w of row v is set when w is within distance D of v."""
    W = (N + 63) // 64
    reach = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N)
    reach[idx, idx >> 6] = np.uint64(1) << (idx & 63).astype(np.uint64)
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[1]):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _cost(nbr, h, N, D):
    """Unordered far pairs plus weighted duplicate edges."""
    reach = _reach_bits(nbr, N, D)
    pc = int(_POP8[reach.view(np.uint8)].sum())
    bad = (N * N - pc) // 2
    dup = int(np.count_nonzero(np.diff(np.sort(nbr[:h], axis=1), axis=1) == 0))
    return bad + _PEN * dup


def _swap(p, nbr, h, l, i1, i2):
    """Exchange the B-targets of A-vertices i1 and i2 in layer l (self-inverse)."""
    a = p[l, i1]
    b = p[l, i2]
    p[l, i1] = b
    p[l, i2] = a
    nbr[i1, l] = h + b
    nbr[i2, l] = h + a
    nbr[h + b, l] = i1
    nbr[h + a, l] = i2


def _anneal(d, h, D, seed, deadline):
    """Anneal a random d-regular bipartite graph on h+h vertices. Returns (n, edges) or None."""
    gen = np.random.default_rng(seed)
    rng = random.Random(seed)
    N = 2 * h
    p = np.stack([gen.permutation(h) for _ in range(d)]).astype(np.int64)
    nbr = np.empty((N, d), dtype=np.int64)
    nbr[:h] = h + p.T
    q = np.empty_like(p)
    for l in range(d):
        q[l, p[l]] = np.arange(h)
    nbr[h:] = q.T

    cost = _cost(nbr, h, N, D)
    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    T0, T1 = 2.0, 0.1
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        l = rng.randrange(d)
        i1, i2 = rng.sample(range(h), 2)
        _swap(p, nbr, h, l, i1, i2)
        c2 = _cost(nbr, h, N, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _swap(p, nbr, h, l, i1, i2)

    edges = [(i, int(nbr[i, l])) for i in range(h) for l in range(d)]
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: anneal random bipartite regular graphs of growing half-size.
    moore = lib.moore_bound(d, D)
    best_h = best_n // 2
    h_try = max(best_h + 1, int(0.4 * moore / 2))
    attempt = 0
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        if h_try <= best_h:
            h_try = best_h + 1
        att_deadline = now + max(1.0, 0.3 * remaining)
        attempt += 1
        s = (seed * 1000003 + attempt) & 0xFFFFFFFF
        res = _anneal(d, h_try, D, s, min(att_deadline, deadline))
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            consider(res[0], res[1])
            best_h = max(best_h, h_try)
            h_try = h_try + max(1, h_try // 100)
        else:
            h_try = max(best_h + 1, int(h_try * 0.95))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
