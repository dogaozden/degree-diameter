import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Structured baselines (cheap, used only for D = 3 and D = 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k, searched by simulated
# annealing with a vectorised (numpy) distance-count cost.
#
# Graph: A_x ~ B_{x*g} for g in S, |S| = d. Left translation is an automorphism,
# so checking the eccentricities of A_0 and B_0 is enough for the whole graph.
# ----------------------------------------------------------------------------

GROUPS_PER_N = 6      # groups tried for each order N before moving on
ANNEAL_ITERS = 2500   # annealing steps per group
GROUP_SLICE = 1.5     # seconds per group, at most
T_START = 3.0
T_END = 0.2


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


def _group_tables(N, m, k, r):
    """Return (TG, inv_arr): TG[g, x] = x*g as an array, inv_arr[g] = g^-1."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    TT = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
    TG = np.ascontiguousarray(TT.T)
    inv_arr = np.array([inv(g) for g in range(N)], dtype=np.int64)
    return TG, inv_arr


def _cost(N, TG, inv_arr, S, D):
    """Number of (source, vertex) pairs not within distance D, from A_0 and from B_0. Zero means valid."""
    rows = [TG[g] for g in S]
    inv_rows = [TG[int(inv_arr[g])] for g in S]
    full = 2 * N
    total = 0
    for side in (0, 1):
        visA = np.zeros(N, dtype=bool)
        visB = np.zeros(N, dtype=bool)
        if side == 0:
            visA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = np.empty(0, dtype=np.int64)
        else:
            visB[0] = True
            fB = np.array([0], dtype=np.int64)
            fA = np.empty(0, dtype=np.int64)
        count = 1
        for _ in range(D):
            if count == full:
                break
            nb = np.zeros(N, dtype=bool)
            if fA.size:
                for row in rows:
                    nb[row[fA]] = True
            na = np.zeros(N, dtype=bool)
            if fB.size:
                for row in inv_rows:
                    na[row[fB]] = True
            nb &= ~visB
            na &= ~visA
            visB |= nb
            visA |= na
            fA = np.nonzero(na)[0]
            fB = np.nonzero(nb)[0]
            added = fA.size + fB.size
            count += added
            if added == 0:
                break
        total += full - count
    return total


def _anneal(N, TG, inv_arr, d, D, rng, iters, deadline):
    """Anneal a connection set S (identity fixed as one element, WLOG) to zero cost."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(N, TG, inv_arr, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T_START * (T_END / T_START) ** (it / max(1, iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _cost(N, TG, inv_arr, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / T):
            S, cur = S2, v
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, max degree 2, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and is always valid.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Sweep bi-Cayley orders N upward from the smallest N that beats the current
    # best (each lift has 2N vertices), annealing over groups for each N.
    N = best[0] // 2 + 1
    while best[0] < moore and time.monotonic() < deadline and 2 * N <= moore:
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:GROUPS_PER_N]:
            now = time.monotonic()
            if now > deadline:
                break
            TG, inv_arr = _group_tables(N, m, k, r)
            slice_end = min(deadline, now + GROUP_SLICE)
            S = _anneal(N, TG, inv_arr, d, D, rng, ANNEAL_ITERS, slice_end)
            if S is not None:
                found = (TG, S)
                break
        if found is not None:
            TG, S = found
            edges = [(x, N + int(TG[g, x])) for x in range(N) for g in S]
            consider(2 * N, edges)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
