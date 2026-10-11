import itertools
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 16   # groups tried per order N within one attempt
ITERS = 4000                  # annealing steps per (group, connection set) try
T_HOT = 3.0                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.2                  # final annealing temperature
WINDOW_FRAC = 0.90            # search only N in [WINDOW_FRAC * top, top] first
BUDGET_START = 1.0            # seconds per (N) attempt in the first pass
BUDGET_CAP = 6.0              # cap on per-attempt seconds as passes fail


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so the diameter is decided by the
# balls around A_0 and B_0.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(N, mul, inv):
    """Vectorised group tables.

    Pall[g, x]   = x * g        (edge A_x -- B_{x g})
    Pinv[g, y]   = y * g^{-1}   (B_y's A-neighbour along generator g)
    """
    T = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.intp)
    invs = np.array([inv(g) for g in range(N)], dtype=np.intp)
    Pall = np.ascontiguousarray(T.T)
    Pinv = np.ascontiguousarray(T[:, invs].T)
    return Pall, Pinv


def _unreached_np(N, Pall, Pinv, S, D):
    """Batched ball computation for sources A_0 and B_0 at once.

    Row 0 of (A, B) tracks the ball around A_0, row 1 the ball around B_0.
    Each BFS layer is one gather over all d connection generators, so a whole
    evaluation costs a handful of numpy calls rather than a Python BFS.
    Returns the number of (source, vertex) pairs at distance > D.
    """
    Ps = Pall[S]          # (d, N): A -> B along each generator
    Qs = Pinv[S]          # (d, N): B -> A along each generator
    A = np.zeros((2, N), dtype=bool)
    B = np.zeros((2, N), dtype=bool)
    A[0, 0] = True
    B[1, 0] = True
    for _ in range(D):
        nA = A | B[:, Ps].any(axis=1)
        nB = B | A[:, Qs].any(axis=1)
        A, B = nA, nB
        if A.all() and B.all():
            break
    reached = int(A.sum()) + int(B.sum())
    return 4 * N - reached


def _anneal(N, Pall, Pinv, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached_np(N, Pall, Pinv, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached_np(N, Pall, Pinv, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        Pall, Pinv = _tables(N, mul, inv)
        S = _anneal(N, Pall, Pinv, d, D, rng, ITERS, deadline)
        if S is not None:
            return Pall, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
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

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 8)
    if top < d + 1:
        return best

    floor = max(d + 1, int(WINDOW_FRAC * top))
    bestN = best_n // 2
    budget = BUDGET_START

    while time.monotonic() < deadline:
        lo = max(floor, bestN + 1)
        cands = list(range(lo, top + 1))
        if not cands:
            break
        rng.shuffle(cands)
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            Pall, S = res
            edges = [(x, N + int(Pall[g, x])) for g in S for x in range(N)]
            consider(2 * N, edges)
            bestN = max(bestN, N)
            success = True
            break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > d + 1:
                floor -= 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
