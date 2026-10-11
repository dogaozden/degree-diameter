import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graphs (diameter 3, valid for D >= 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bold change: k = 1 bi-Cayley graphs over small non-abelian groups.
#
# Group G = Z_m x| Z_k with (a,b)(c,e) = (a + r^b c, b + e), coded as a*k + b.
# Connection set S = {s_1..s_d} (distinct elements of G). The graph has
#   A_g ~ B_{g s} for s in S,   vertices A_g = g, B_h = N + h,  N = |G|.
# Left multiplication is an automorphism, so the A-side and B-side are each
# vertex-transitive. Hence the graph is d-regular and simple, and has diameter
# <= D iff the radius-D balls around A_e and B_e cover everything.
# S is found by simulated annealing that minimises the number of uncovered
# (source, vertex) pairs, using numpy boolean BFS.
# ----------------------------------------------------------------------------

def _groups(N):
    """All (m, k, r) with m*k = N giving Z_m x| Z_k (r = 1 for k = 1 is the cyclic group)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 1:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        if m == 1:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Multiplication table T[x, y] = x*y and inverse array for Z_m x| Z_k; identity is 0."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    Bv = (b[:, None] + b[None, :]) % k
    T = A * k + Bv
    inv = np.argmax(T == 0, axis=1).astype(np.int64)
    return T, inv


def _unr(NA, NB, N, D, src):
    """Number of vertices not within distance D of the source (0 = A_e, 1 = B_e)."""
    visA = np.zeros(N, dtype=bool)
    visB = np.zeros(N, dtype=bool)
    fA = np.zeros(N, dtype=bool)
    fB = np.zeros(N, dtype=bool)
    if src == 0:
        fA[0] = True
        visA[0] = True
    else:
        fB[0] = True
        visB[0] = True
    for _ in range(D):
        nB = np.zeros(N, dtype=bool)
        if fA.any():
            nB[NA[fA].ravel()] = True
        nB &= ~visB
        nA = np.zeros(N, dtype=bool)
        if fB.any():
            nA[NB[fB].ravel()] = True
        nA &= ~visA
        if not nA.any() and not nB.any():
            break
        visA |= nA
        visB |= nB
        fA, fB = nA, nB
    return 2 * N - int(visA.sum()) - int(visB.sum())


def _cost(T, inv, N, D, Sa):
    """Total uncovered pairs from A_e and from B_e for connection set Sa (numpy array)."""
    NA = T[:, Sa]
    NB = T[:, inv[Sa]]
    return _unr(NA, NB, N, D, 0) + _unr(NA, NB, N, D, 1)


def _anneal(T, inv, N, d, D, rng, deadline):
    """Simulated annealing over d-subsets of G. Returns a valid connection set (list) or None."""
    S = rng.sample(range(N), d)
    c = _cost(T, inv, N, D, np.array(S, dtype=np.int64))
    if c == 0:
        return S
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        temp = 0.05 + 1.5 * (1.0 - frac)
        pos = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = list(S)
        S2[pos] = x
        c2 = _cost(T, inv, N, D, np.array(S2, dtype=np.int64))
        if c2 == 0:
            return S2
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, c = S2, c2


def _edges(T, N, S):
    """Edges of the bi-Cayley graph: A_g = g joins B_h = N + h for h = g*s, s in S."""
    Sa = np.asarray(S, dtype=np.int64)
    rows = T[:, Sa].tolist()
    out = []
    for g in range(N):
        for h in rows[g]:
            out.append((g, N + h))
    return 2 * N, out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D < 3 or d < 2:
        return best

    try:
        moore = lib.moore_bound(d, D)
        cache = {}
        while True:
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 0.5:
                break
            lo = max(best[0] // 2 + 1, int(0.2 * moore / 2), d)
            lo = min(lo, 1000)
            hi = min(lo + 10, 1000)
            N = rng.randint(lo, hi)
            if N < d:
                continue
            if N not in cache:
                cache[N] = _groups(N)
            gl = cache[N]
            if not gl:
                continue
            m, k, r = rng.choice(gl)
            T, inv = _table(m, k, r)
            S = _anneal(T, inv, N, d, D, rng, min(deadline, now + 5.0))
            if S is not None:
                n2, e2 = _edges(T, N, S)
                consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    return best
