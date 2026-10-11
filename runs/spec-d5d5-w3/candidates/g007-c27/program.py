import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k.
#
# A bi-Cayley graph on a group G of order N has vertices A_x, B_y (x, y in G)
# with A_x ~ B_{x*g} for g in S, |S| = d. Left translation is an automorphism,
# so a BFS from A_0 and from B_0 decides the diameter. The BFS is vectorised
# with numpy: each level is a fancy-indexed gather from the multiplication table.
# This replaces the per-element Python BFS of the earlier search, so the
# hill-climb can afford many more steps per second.
#
# Identity 0 is always in S (WLOG, by relabelling the B side).
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _group_tables(m, k, r):
    """Cached (N, T, invs): T[x, g] = x*g as an int64 array, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _GROUP_CACHE.get(key)
    if hit is not None:
        return hit
    N, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
    invs = np.array([inv(g) for g in range(N)], dtype=np.int64)
    if len(_GROUP_CACHE) > 64:
        _GROUP_CACHE.clear()
    val = (N, T, invs)
    _GROUP_CACHE[key] = val
    return val


def _groups(N):
    """All semidirect parameters (m, k, r) with m*k = N and r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(N, T, Sarr, invArr, D):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0.

    Frontier expansion is vectorised:
      A_x -> B_{x g} for g in S, so from A-frontier fA we gather T[fA, S];
      B_y -> A_{y g^-1} for g in S, so from B-frontier fB we gather T[fB, S^-1].
    """
    total = 0
    for start_is_a in (True, False):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if start_is_a:
            seenA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = np.empty(0, dtype=np.int64)
        else:
            seenB[0] = True
            fA = np.empty(0, dtype=np.int64)
            fB = np.array([0], dtype=np.int64)
        count = 1
        for _ in range(D):
            if fA.size == 0 and fB.size == 0:
                break
            cand_b = T[np.ix_(fA, Sarr)].ravel()
            cand_a = T[np.ix_(fB, invArr)].ravel()
            nb = np.unique(cand_b[~seenB[cand_b]])
            na = np.unique(cand_a[~seenA[cand_a]])
            seenB[nb] = True
            seenA[na] = True
            count += nb.size + na.size
            fA, fB = na, nb
        total += 2 * N - count
    return total


def _score(N, T, invs, S, D):
    Sarr = np.array(S, dtype=np.int64)
    return _unreached(N, T, Sarr, invs[Sarr], D)


def _climb(N, T, invs, d, D, iters, deadline, rng):
    """Hill-climb a connection set S (|S| = d, 0 fixed) to zero unreached pairs.

    Sideways moves are accepted, and worse moves with small probability so the
    walk can leave local minima. Returns S, or None if no zero-cost set was found.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _score(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _score(N, T, invs, S2, D)
        if v <= cur or rng.random() < 0.02:
            S, cur = S2, v
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baseline for D = 3: projective plane incidence graph, which is
    # extremal when d - 1 is a prime power.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    moore = lib.moore_bound(d, D)

    # Main search: bi-Cayley lifts with 2N vertices, N sweeping just above the
    # current best half-order.
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(4)
        if N < d:
            N = d
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k, r in groups[:6]:
            if time.monotonic() > deadline:
                break
            _, T, invs = _group_tables(m, k, r)
            S = _climb(N, T, invs, d, D, 3000, deadline, rng)
            if S is not None:
                Tl = T.tolist()
                edges = [(x, N + Tl[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
