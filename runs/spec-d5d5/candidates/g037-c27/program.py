import math
import random
import time
from itertools import product

import numpy as np

import lib

# ----------------------------------------------------------------------------
# Search parameters
# ----------------------------------------------------------------------------
ITERS = 2500                 # annealing steps per (group, voltage) try
T_HOT = 2.0                  # initial temperature (unreached-pair units)
T_COLD = 0.1                 # final temperature
GROUPS_PER_CAND = 8          # groups tried per (base, N) candidate
MULTI_ORBIT_BASES = (1, 2, 3, 4, 6)   # number of A-orbits (a); total order = 2*a*N
WINDOW = 24                  # phase 2 only targets totals in (best, best + WINDOW]

# ----------------------------------------------------------------------------
# New idea: "layered base lifts" with vectorised reach-checking.
#
# A base bipartite graph has a A-vertices and a B-vertices, and is the union of
# d perfect matchings ("layers") sigma_0..sigma_{d-1} of {0..a-1}. Each dart
# (A_i -> B_{sigma_k(i)}) carries a voltage g in a finite group G of order N.
# The lift has 2aN vertices, is bipartite, and every vertex has degree <= d.
# Left multiplication by G is an automorphism, so the diameter is decided by
# eccentricities from the 2a base representatives only.
#
# Each candidate is scored by the number of (representative, vertex) pairs at
# distance > D. That count is computed for all vertices at once with numpy
# (boolean reach matrix, one gather per distance layer), which makes annealing
# over voltages fast. a = 1 reproduces the usual bi-Cayley search.
# ----------------------------------------------------------------------------


def _is_prime_power(q):
    return lib.is_prime_power(q)


def _pg_best(d):
    for q in range(d - 1, 1, -1):
        if _is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in product(range(q), repeat=4)
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


def _gq_best(d):
    for q in range(min(d - 1, 5), 1, -1):
        if _is_prime_power(q):
            return _gq_w(q)
    return None


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


_TABLE_CACHE = {}


def _tables(m, k, r, N):
    """Multiplication table T[x, g] = x*g (numpy and list), and inverses, for the group."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is None:
        _, mul, inv = lib.semidirect_group(m, k, r)
        T_list = [[mul(x, g) for g in range(N)] for x in range(N)]
        T = np.array(T_list, dtype=np.int64)
        invs = [inv(g) for g in range(N)]
        hit = (T, T_list, invs)
        _TABLE_CACHE[key] = hit
    return hit


def _nbr(a, N, d, perms, volt, T, invs):
    """Neighbour array (n, d): slot k of each lift vertex is its neighbour across layer k."""
    n = 2 * a * N
    nbr = np.repeat(np.arange(n, dtype=np.int64)[:, None], d, axis=1)
    for k in range(d):
        sig = perms[k]
        for i in range(a):
            j = sig[i]
            g = volt[k][i]
            # A_i fibre: (i, x) -> (a+j, x*g)
            nbr[i * N:(i + 1) * N, k] = (a + j) * N + T[:, g]
            # B_j fibre: (a+j, y) -> (i, y*g^-1)
            nbr[(a + j) * N:(a + j + 1) * N, k] = i * N + T[:, invs[g]]
    return nbr


def _bad(nbr, s, N, D):
    """Number of (base representative, vertex) pairs at distance > D (0 iff diameter <= D)."""
    n = nbr.shape[0]
    B = np.zeros((n, s), dtype=bool)
    idx = np.arange(s)
    B[idx * N, idx] = True          # representatives are identity fibre elements
    for _ in range(D):
        B2 = B | B[nbr].any(axis=1)
        if int(B2.sum()) == int(B.sum()):
            B = B2
            break
        B = B2
    return n * s - int(B.sum())


def _anneal(a, N, d, D, T, invs, perms, rng, deadline):
    s = 2 * a
    volt = [[rng.randrange(N) for _ in range(a)] for _ in range(d)]
    cur = _bad(_nbr(a, N, d, perms, volt, T, invs), s, N, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        k = rng.randrange(d)
        i = rng.randrange(a)
        new = rng.randrange(N)
        old = volt[k][i]
        if new == old:
            continue
        volt[k][i] = new
        v = _bad(_nbr(a, N, d, perms, volt, T, invs), s, N, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            volt[k][i] = old
    return cur, volt


def _edges(a, N, d, perms, volt, T_list):
    E = set()
    for k in range(d):
        for i in range(a):
            j = perms[k][i]
            g = volt[k][i]
            for x in range(N):
                E.add((i * N + x, (a + j) * N + T_list[x][g]))
    return list(E)


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for base size a; return (n, edges) with diameter <= D, or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_CAND]:
        if time.monotonic() >= deadline:
            return None
        T, T_list, invs = _tables(m, k, r, N)
        perms = [rng.sample(range(a), a) for _ in range(d)]
        cur, volt = _anneal(a, N, d, D, T, invs, perms, rng, deadline)
        if cur == 0:
            return 2 * a * N, _edges(a, N, d, perms, volt, T_list)
    return None


def _window(moore, best_n):
    out = []
    for a in MULTI_ORBIT_BASES:
        for N in range(7, moore // (2 * a) + 1):
            T = 2 * a * N
            if best_n < T <= best_n + WINDOW:
                out.append((T, a, N))
    out.sort()
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total_deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact record family for D = 3.
    if D == 3 and _is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < total_deadline:
        gq = _gq_best(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)

    # Phase 1: bi-Cayley (a = 1) lifts, descending from the top of the range.
    p1_deadline = start + 0.2 * 0.8 * time_limit
    Nmax1 = moore // 2
    top = min(Nmax1, Nmax1 // 2 + 6)
    for N in range(top, d, -1):
        if time.monotonic() >= p1_deadline:
            break
        res = _attempt(1, N, d, D, rng, min(p1_deadline, time.monotonic() + 0.35))
        if res is not None:
            consider(*res)
            break

    # Phase 2: multi-orbit layered lifts for totals just above the current best.
    budget = 0.5
    while time.monotonic() < total_deadline:
        cands = _window(moore, best_n)
        if not cands:
            break
        progressed = False
        for T, a, N in cands:
            now = time.monotonic()
            if now >= total_deadline:
                break
            if T <= best_n:
                continue
            res = _attempt(a, N, d, D, rng, min(total_deadline, now + budget))
            if res is not None:
                consider(*res)
                progressed = True
                break
        if not progressed:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
