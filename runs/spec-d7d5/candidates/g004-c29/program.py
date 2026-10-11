import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact algebraic families (used for calibration-style cases and fallbacks).
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
# Group choices.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _popcount(R):
    return int(_POP8[R.view(np.uint8)].sum())


def _groups_of_order(G, rng, limit=4):
    """Candidate semidirect products Z_m x| Z_k2 (as (m, k2, r)) with m*k2 = G."""
    out = []
    for k2 in range(1, min(G, 40) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            continue
        rng.shuffle(cands)
        out += [(m, k2, r) for r in cands[:limit]]
    return out


# ----------------------------------------------------------------------------
# NEW ROUTINE: greedy seeding followed by time-scheduled annealing for
# bi-Cayley lifts over a finite group.
#
# Structure: k base vertices per side, d layers. Layer l is a permutation
# p_l of range(k), and dart (l, i) carries a voltage s in the group. Vertex
# A_{i,g} is joined to B_{p_l(i), g*s}. Each layer gives every vertex one edge.
#
# Unlike the random-start annealing, the darts are first filled one at a time.
# Each dart takes the best of a random sample of voltages, scored on the
# partial graph (unfilled darts act as harmless self-loops in the reach
# computation). The result seeds annealing on the full graph. Cost is the
# exact number of ordered vertex pairs at distance > D, over all N vertices,
# plus a penalty for duplicate (i, j, s) darts.
# ----------------------------------------------------------------------------

def _lift_search(d, D, k, G, mul, rng, deadline):
    N = 2 * k * G
    W = (N + 63) // 64
    base = np.zeros((N, W), dtype=np.uint64)
    v = np.arange(N, dtype=np.int64)
    base[v, v // 64] = np.uint64(1) << (v % 64).astype(np.uint64)

    ar = np.arange(G, dtype=np.int64)
    cache = {}

    def perm(s):
        hit = cache.get(s)
        if hit is None:
            pm = np.fromiter((int(mul(g, s)) for g in range(G)), dtype=np.int64, count=G)
            inv = np.empty(G, dtype=np.int64)
            inv[pm] = ar
            hit = (pm, inv)
            cache[s] = hit
        return hit

    layers = [rng.sample(range(k), k) for _ in range(d)]
    nb = np.empty((N, d), dtype=np.int64)
    nb[:] = np.arange(N, dtype=np.int64)[:, None]
    S = [[None] * k for _ in range(d)]

    def set_dart(l, i, s):
        j = layers[l][i]
        a0 = i * G
        b0 = (k + j) * G
        if s is None:
            nb[a0:a0 + G, l] = ar + a0
            nb[b0:b0 + G, l] = ar + b0
        else:
            pm, inv = perm(s)
            nb[a0:a0 + G, l] = b0 + pm
            nb[b0:b0 + G, l] = a0 + inv
        S[l][i] = s

    def dup_count():
        seen = set()
        dup = 0
        for l in range(d):
            for i in range(k):
                s = S[l][i]
                if s is None:
                    continue
                key = (i, layers[l][i], s)
                if key in seen:
                    dup += 1
                else:
                    seen.add(key)
        return dup

    def cost():
        R = base
        for _ in range(D):
            R = R | np.bitwise_or.reduce(R[nb], axis=1)
        reached = _popcount(R)
        return N * N - reached + _PENALTY * dup_count()

    # Greedy seeding: fill each dart with the best sampled voltage.
    darts = [(l, i) for l in range(d) for i in range(k)]
    rng.shuffle(darts)
    C = min(G, 24)
    for (l, i) in darts:
        if time.monotonic() > deadline:
            return None
        bs = None
        bc = None
        for s in rng.sample(range(G), C):
            set_dart(l, i, s)
            c = cost()
            if bc is None or c < bc:
                bc = c
                bs = s
        set_dart(l, i, bs)

    cur = cost()

    # Annealing on the complete graph, temperature scheduled by elapsed time.
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T_start = 0.02 * N + 1.0
    T_end = 0.3
    while cur != 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - t0) / span
        temp = T_start * (T_end / T_start) ** frac
        l = rng.randrange(d)
        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        set_dart(l, i, new)
        c2 = cost()
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            set_dart(l, i, old)

    if cur != 0:
        return None
    edges = set()
    for x in range(N):
        for y in nb[x].tolist():
            if y != x:
                edges.add((x, y) if x < y else (y, x))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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

    # Main search: greedy-seeded annealing of bi-Cayley lifts over semidirect products.
    if D >= 3 and d >= 2:
        try:
            while time.monotonic() < deadline:
                now = time.monotonic()
                remaining = deadline - now
                k = rng.choice([1, 1, 1, 2, 2, 3])
                G0 = best_n // (2 * k) + 1
                G = G0 + rng.randrange(0, max(2, G0 // 40) + 1)
                cands = _groups_of_order(G, rng)
                if not cands:
                    continue
                m, k2, r = rng.choice(cands)
                try:
                    order, mul, _ = lib.semidirect_group(m, k2, r)
                except ValueError:
                    continue
                slice_end = min(deadline, now + max(2.0, min(10.0, 0.3 * remaining)))
                res = _lift_search(d, D, k, order, mul, rng, slice_end)
                if res is not None:
                    consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
