import itertools
import math
import random
import time

import numpy as np

import lib

ITERS = 700                   # annealing steps per (group, connection set) try
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.1                  # final annealing temperature
MAX_GROUPS = 16               # groups tried per order N within one attempt
SAFETY_FRAC = 0.85            # fraction of time_limit we are willing to use
SAFETY_SECS = 6.0             # absolute margin kept free before time_limit


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
# Bi-Cayley search over groups Z_m x|_r Z_k of order N.
#
# Vertices A_x and B_y (x, y in G); edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so BFS from A_0 and B_0 decides the
# diameter. The identity (index 0) is WLOG in S.
#
# Bold change relative to the parent: the search range is extended far above
# the parent's cap (Nmax // 2 + 6) up to the full Moore-derived bound, the
# group tables are built vectorized, and the connection-set check runs in numpy.
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


def _group_tables(m, k, r):
    """Vectorized multiplication table M[x, g] = x*g and inverse array I[g] for Z_m x|_r Z_k."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    nb = (-b) % k
    I = ((-pw[nb] * a) % m) * k + nb
    return M, I


def _unreached(N, M, I, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sarr = np.asarray(S, dtype=np.int64)
    Sinv = I[Sarr]
    total = 0
    for src in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if src == 0:
            seenA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = np.empty(0, dtype=np.int64)
        else:
            seenB[0] = True
            fA = np.empty(0, dtype=np.int64)
            fB = np.array([0], dtype=np.int64)
        count = 1
        for _ in range(D):
            if fA.size:
                nB = np.unique(M[fA][:, Sarr].ravel())
                nB = nB[~seenB[nB]]
            else:
                nB = np.empty(0, dtype=np.int64)
            if fB.size:
                nA = np.unique(M[fB][:, Sinv].ravel())
                nA = nA[~seenA[nA]]
            else:
                nA = np.empty(0, dtype=np.int64)
            seenB[nB] = True
            seenA[nA] = True
            count += nB.size + nA.size
            fA, fB = nA, nB
            if fA.size == 0 and fB.size == 0:
                break
        total += 2 * N - count
    return total


def _anneal(N, M, I, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, M, I, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, M, I, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        M, I = _group_tables(m, k, r)
        S = _anneal(N, M, I, d, D, rng, ITERS, deadline)
        if S is not None:
            return M, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(SAFETY_FRAC * time_limit, time_limit - SAFETY_SECS)
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

    hi = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    budget = 0.4
    while time.monotonic() < deadline:
        # Only orders that would beat the current best are useful.
        lo = max(d + 1, best_n // 2 + 1)
        if lo > hi:
            break
        progressed = False
        N = lo
        while N <= hi and time.monotonic() < deadline:
            att_deadline = min(deadline, time.monotonic() + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is not None:
                M, S = res
                Mrows = M.tolist()
                edges = [(x, N + Mrows[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
                progressed = True
            N += 1
        if not progressed:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
