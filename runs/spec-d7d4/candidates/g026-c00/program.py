import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective plane (D = 3) and generalized quadrangle W(q) (D >= 4).
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# New construction: voltage lifts over small groups, found by simulated annealing.
#
# Base graph: p vertices on side A and p on side B, joined by d darts per A-vertex
# (circulant dart pattern, so every base vertex has degree d). Each dart carries a
# voltage g in a group G of order N, and the lift has 2pN vertices. Left
# multiplication by h is an automorphism of the lift, so every fibre is vertex
# transitive. The number of bad pairs is therefore computed from only 2p sources
# (the identity of each fibre), with a vectorised ball expansion. Cost is the
# total number of (source, far vertex) pairs; zero means diameter <= D.
# ----------------------------------------------------------------------------

def _pattern(p, d):
    """Circulant dart pattern on p x p base pairs: row and column sums are both d."""
    pat = []
    r = d % p
    for i in range(p):
        for j in range(p):
            m = d // p + (1 if (j - i) % p < r else 0)
            pat.extend([(i, j)] * m)
    return pat


def _group_specs(N, rng, cap):
    """Specs of groups of order N: the cyclic group, and Z_m x|_r Z_k with m*k = N."""
    specs = [("cyc",)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append(("sd", m, k, r))
    rng.shuffle(specs)
    return specs[:cap]


def _table(spec, N):
    """Multiplication table T[x, y] = x*y for a group of order N with identity 0."""
    if spec[0] == "cyc":
        ar = np.arange(N, dtype=np.int64)
        return (ar[:, None] + ar[None, :]) % N
    _, m, k, r = spec
    _, mul, _ = lib.semidirect_group(m, k, r)
    return np.array([[mul(x, y) for y in range(N)] for x in range(N)], dtype=np.int64)


def _cost(p, N, pat, perms, D):
    """Sum over the 2p fibre sources of the number of vertices at distance > D."""
    S = 2 * p
    R = np.zeros((S, S, N), dtype=bool)
    idx = np.arange(S)
    R[idx, idx, 0] = True  # source s is (fibre s, identity)
    for _ in range(D):
        NR = R.copy()
        for (i, j), perm in zip(pat, perms):
            pj = p + j
            NR[:, pj, perm] |= R[:, i, :]
            NR[:, i, :] |= R[:, pj, perm]
        R = NR
    reached = R.sum(axis=(1, 2))
    return int(np.sum(2 * p * N - reached))


def _anneal(p, N, T, pat, D, end, rng):
    """Anneal the voltages until the cost is 0 or the time slice ends. Returns (cost, voltages)."""
    gs = [rng.randrange(N) for _ in pat]
    perms = [T[:, g].copy() for g in gs]
    cur = _cost(p, N, pat, perms, D)
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            break
        frac = (now - t0) / span
        temp = 2.0 * (0.03 / 2.0) ** frac
        k = rng.randrange(len(pat))
        ng = rng.randrange(N)
        if ng == gs[k]:
            continue
        og, op = gs[k], perms[k]
        gs[k] = ng
        perms[k] = T[:, ng].copy()
        c = _cost(p, N, pat, perms, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            gs[k] = og
            perms[k] = op
    return cur, gs


def _lift_graph(p, N, T, pat, gs):
    darts = [(i, p + j, g) for (i, j), g in zip(pat, gs)]
    return lib.group_lift(2 * p, darts, N, lambda x, g: int(T[x, g]))


def _lift_search(d, D, box, deadline, rng, moore):
    """Raise the order one even step at a time, annealing lifts until one succeeds."""
    cache = {}

    def tables(N):
        if N not in cache:
            cache[N] = [(sp, _table(sp, N)) for sp in _group_specs(N, rng, 5)]
        return cache[N]

    O = box[0][0] + 1
    if O % 2:
        O += 1
    rnd = 0
    while time.monotonic() < deadline and O <= moore:
        configs = []
        for p in range(1, 7):
            if O % (2 * p) == 0 and O // (2 * p) >= 2:
                N = O // (2 * p)
                pat = _pattern(p, d)
                for _, T in tables(N):
                    configs.append((p, N, T, pat))
        if not configs:
            O += 2
            rnd = 0
            continue
        slice_len = 0.25 * (2 ** min(rnd, 8))
        found = None
        for p, N, T, pat in configs:
            now = time.monotonic()
            if now >= deadline:
                break
            cost, gs = _anneal(p, N, T, pat, D, min(deadline, now + slice_len), rng)
            if cost == 0:
                n, e = _lift_graph(p, N, T, pat, gs)
                if n > box[0][0] and lib.is_valid(n, e, d, D):
                    found = (n, e)
                    break
        if found:
            box[0] = found
            O = found[0] + 2
            rnd = 0
        else:
            rnd += 1


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        fallback = (1, [])
    box = [fallback]

    def consider(g):
        n, e = g
        if n > box[0][0] and lib.is_valid(n, e, d, D):
            box[0] = (n, e)

    if D == 3:
        q = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
        if q is not None:
            consider(lib.projective_plane_incidence(q))
    elif D >= 4:
        q = next((q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)), None)
        if q is not None:
            consider(_gq_w(q))

    moore = lib._moore_bound(d, D)
    if box[0][0] >= moore:
        return box[0]

    try:
        _lift_search(d, D, box, deadline, rng, moore)
    except Exception:
        pass

    return box[0]
