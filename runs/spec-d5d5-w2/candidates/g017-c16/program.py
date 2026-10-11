import itertools
import math
import random
import time

import numpy as np

import lib

# Multi-orbit voltage lifts over semidirect products Z_m x| Z_k.
# The base graph has r A-orbits and r B-orbits. Each A-orbit sends d darts and
# each B-orbit receives d darts, so every vertex has degree d. Dart (i, j, g)
# joins A_{i,x} to B_{j, x*g} for all x in G. Left multiplication is an
# automorphism, so eccentricities only need sources A_{i,e} and B_{j,e}.

ITERS = 1500
T_HOT = 6.0
T_COLD = 0.3
GROUPS_PER_ATTEMPT = 4
ATTEMPT_BUDGET = 3.0
WINDOW = 3
R_LIST = [1, 2, 3, 4, 5, 6, 8, 10, 12]


# ----------------------------------------------------------------------------
# Fallback families (fast, validated before use).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit search.
# ----------------------------------------------------------------------------

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


def _cost(r, N, D, T, darts):
    """Number of (source, vertex) pairs at distance more than D over the 2r orbit sources."""
    arr = np.array(darts, dtype=np.int64)
    I, J, G = arr[:, 0], arr[:, 1], arr[:, 2]
    V = 2 * r * N
    ar = np.arange(N, dtype=np.int64)
    a = (I[:, None] * N + ar[None, :]).ravel()
    b = (r * N + J[:, None] * N + T[:, G].T).ravel()
    Q = np.zeros((V, V), dtype=np.float32)
    Q[a, b] = 1.0
    Q[b, a] = 1.0
    idx = np.arange(V)
    Q[idx, idx] = 1.0
    S = 2 * r
    src = np.array([i * N for i in range(r)] + [r * N + j * N for j in range(r)],
                   dtype=np.int64)
    cur = np.zeros((S, V), dtype=np.float32)
    cur[np.arange(S), src] = 1.0
    for _ in range(D):
        cur = ((cur @ Q) > 0).astype(np.float32)
    return int(S * V - cur.sum())


def _init(r, d, N, rng):
    """d random layers of permutations; each A-orbit and B-orbit gets exactly d darts."""
    for _ in range(50):
        darts = []
        for _layer in range(d):
            perm = list(range(r))
            rng.shuffle(perm)
            for i in range(r):
                darts.append((i, perm[i], rng.randrange(N)))
        if len(set(darts)) == len(darts):
            return darts
    return None


def _anneal(r, d, N, D, T, rng, iters, deadline):
    """Anneal darts so every source reaches all vertices within distance D."""
    darts = _init(r, d, N, rng)
    if darts is None:
        return None
    R = len(darts)
    cur = _cost(r, N, D, T, darts)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        new = list(darts)
        if R < 2 or rng.random() < 0.5:
            k = rng.randrange(R)
            i, j, _ = new[k]
            new[k] = (i, j, rng.randrange(N))
        else:
            k1, k2 = rng.sample(range(R), 2)
            i1, j1, g1 = new[k1]
            i2, j2, g2 = new[k2]
            if j1 == j2:
                continue
            new[k1] = (i1, j2, g1)
            new[k2] = (i2, j1, g2)
        if len(set(new)) != R:
            continue
        v = _cost(r, N, D, T, new)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _attempt(r, d, D, N, rng, deadline):
    """Try groups of order N for an r-orbit lift; return (darts, T) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, rr in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, rr)
        T = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
        darts = _anneal(r, d, N, D, T, rng, ITERS, deadline)
        if darts is not None:
            return darts, T
    return None


def _edges(r, N, T, darts):
    """Edges of the lift: A-vertices are 0..rN-1, B-vertices are rN..2rN-1."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, r * N + j * N + int(T[x, g])))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(2.0, min(0.9 * time_limit, time_limit - 5.0))
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

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    moore = lib.moore_bound(d, D)

    # Ascending search: every success raises the bar for all orbit counts.
    while time.monotonic() < deadline:
        for r in R_LIST:
            if time.monotonic() >= deadline:
                break
            lo = max(2, best_n // (2 * r) + 1)
            if 2 * r * lo > moore:
                continue
            N = lo + rng.randrange(WINDOW)
            if 2 * r * N > moore:
                N = lo
            att_deadline = min(deadline, time.monotonic() + ATTEMPT_BUDGET)
            res = _attempt(r, d, D, N, rng, att_deadline)
            if res is None:
                continue
            darts, T = res
            consider(2 * r * N, _edges(r, N, T, darts))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
