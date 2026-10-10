import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 3000                  # annealing iterations per attempt (lift search)
ATTEMPTS = 3                  # annealing restarts per (s, m)
S_LIST = (1, 2, 3, 4, 5, 6)   # base vertices per side for the lift search
PG_TRUST_N = 12000            # above this size, skip the re-check of the PG construction
HAAR_SHARE = 0.55             # fraction of the working time given to the Haar search


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Phase 1 (new): bi-circulant Haar graphs H(Z_m, S), |S| = d, searched with
# bitmask sumset BFS. Vertex a_i ~ b_{i+s} for s in S. Z_m acts transitively on
# each side, so checking BFS from a_0 and from b_0 decides the diameter.
# ----------------------------------------------------------------------------

def _popcount(x):
    return bin(x).count("1")


def _haar_cost(S, negS, m, full, D):
    """Number of (source, vertex) pairs at distance > D, for sources a_0 and b_0. Zero iff diameter <= D."""
    total = 0
    for src_a in (True, False):
        if src_a:
            fa, fb, ra, rb = 1, 0, 1, 0
        else:
            fa, fb, ra, rb = 0, 1, 0, 1
        for _ in range(D):
            if not (fa or fb):
                break
            nb = 0
            if fa:
                for s in S:
                    nb |= ((fa << s) | (fa >> (m - s))) & full
            na = 0
            if fb:
                for s in negS:
                    na |= ((fb << s) | (fb >> (m - s))) & full
            nb &= full & ~rb
            na &= full & ~ra
            rb |= nb
            ra |= na
            fa, fb = na, nb
        total += 2 * m - _popcount(ra) - _popcount(rb)
    return total


def _haar_try(m, d, D, rng, deadline):
    """Local search for a connection set S of size d in Z_m giving diameter <= D. Returns sorted S or None."""
    if m < d:
        return None
    full = (1 << m) - 1
    S = [0] + rng.sample(range(1, m), d - 1)   # WLOG 0 in S (translation is an isomorphism)
    inS = set(S)
    cur = _haar_cost(S, [(-s) % m for s in S], m, full, D)
    steps = 0
    while cur > 0:
        steps += 1
        if (steps & 63) == 0 and time.monotonic() > deadline:
            return None
        idx = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in inS:
            continue
        old = S[idx]
        S[idx] = new
        c = _haar_cost(S, [(-s) % m for s in S], m, full, D)
        if c <= cur or rng.random() < 0.03:
            inS.discard(old)
            inS.add(new)
            cur = c
        else:
            S[idx] = old
    return sorted(S)


def _haar_search(d, D, rng, deadline, hi):
    """Bisection on m in [d, hi] using Haar local search. Returns (m, S) for the largest success found."""
    best = None
    lo, up = d - 1, hi + 1
    while up - lo > 1:
        now = time.monotonic()
        if now >= deadline:
            break
        mid = (lo + up) // 2
        slice_end = now + max(0.05, min((deadline - now) / 3.0, 2.0))
        S = _haar_try(mid, d, D, rng, min(slice_end, deadline))
        if S is not None:
            lo = mid
            best = (mid, S)
        else:
            up = mid
    return best


# ----------------------------------------------------------------------------
# Phase 2 (parent): voltage lifts of small base multigraphs, by annealing.
# ----------------------------------------------------------------------------

def _neighbors(P, Pinv, V, s, m):
    """Neighbour table (n x d) of the Z_m lift of a d-regular bipartite base on s+s vertices."""
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + (g + int(V[k, i])) % m
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + (g - int(V[k, i])) % m
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal(s, m, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(m)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _anneal_restarts(s, m, d, D, rng, deadline):
    for _ in range(ATTEMPTS):
        if time.monotonic() >= deadline:
            break
        st = _anneal(s, m, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _graph(s, m, P, V, d):
    """Materialise the lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest m (by doubling then bisection) whose lift passes annealing."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _anneal_restarts(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = start + max(0.5, 0.8 * time_limit - 1.0)

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    if D < 2 or d < 1:
        return fallback

    best = fallback

    # D = 3: incidence graph of PG(2, q), q the largest prime power <= d - 1.
    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None and pg[0] > best[0]:
            ok = pg[0] > PG_TRUST_N or lib.is_valid(pg[0], pg[1], d, D)
            if ok:
                best = pg
                if lib.is_prime_power(d - 1):
                    return best

    rng = random.Random(seed)

    # Phase 1: bi-circulant Haar graphs with sumset-based search.
    if d >= 2:
        hi = min(N_CAP // 2, lib._moore_bound(d, D) // 2)
        if hi >= d:
            now = time.monotonic()
            hd = now + HAAR_SHARE * max(0.0, total - now)
            res = _haar_search(d, D, rng, hd, hi)
            if res is not None:
                m, S = res
                n, e = lib.haar_graph(m, S)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)

    # Phase 2: voltage-lift search over Z_m with s base vertices per side.
    if d >= 2:
        cap = min(N_CAP, lib._moore_bound(d, D))
        lift = None  # (n, s, m, P, V)
        for idx, s in enumerate(S_LIST):
            now = time.monotonic()
            if now >= total:
                break
            slice_end = now + (total - now) / (len(S_LIST) - idx)
            res = _search(s, d, D, rng, slice_end, cap)
            if res is not None:
                m, P, V = res
                n = 2 * s * m
                if lift is None or n > lift[0]:
                    lift = (n, s, m, P, V)
        if lift is not None and lift[0] > best[0]:
            n, e = _graph(lift[1], lift[2], lift[3], lift[4], d)
            if lib.is_valid(n, e, d, D):
                best = (n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
