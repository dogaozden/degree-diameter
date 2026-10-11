import math
import random
import time

import numpy as np

import lib

# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k with one base vertex per side.
# A_x ~ B_{x*s} for s in S (|S| = d). Left translation is an automorphism, so the
# diameter check only needs BFS from A_e and B_e. The BFS runs on numpy arrays.
# The order N is found by bisection between the known-valid lower bound and the
# Moore bound, not by a sweep. Non-abelian groups are tried first.

_TABLES = {}


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


def _table(m, k, r):
    """Cached (order, Tc, invs): Tc[g, x] = x*g, invs[g] = g^-1, identity = element 0."""
    key = (m, k, r)
    hit = _TABLES.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        T[x] = [mul(x, g) for g in range(order)]
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    Tc = np.ascontiguousarray(T.T)
    val = (order, Tc, invs)
    if len(_TABLES) >= 40:
        _TABLES.clear()
    _TABLES[key] = val
    return val


def _unreached(N, Tc, invs, S, D):
    """Number of (source, vertex) pairs not within distance D, for sources A_e and B_e."""
    Sl = [int(s) for s in S]
    Sinv = [int(invs[s]) for s in S]
    total = 0
    for side in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if side == 0:
            seenA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = np.zeros(0, dtype=np.int64)
        else:
            seenB[0] = True
            fA = np.zeros(0, dtype=np.int64)
            fB = np.array([0], dtype=np.int64)
        for _ in range(D):
            if fA.size == 0 and fB.size == 0:
                break
            nB = np.zeros(N, dtype=bool)
            for s in Sl:
                nB[Tc[s][fA]] = True           # A_x -> B_{x s}
            nB &= ~seenB
            nA = np.zeros(N, dtype=bool)
            for h in Sinv:
                nA[Tc[h][fB]] = True           # B_y -> A_{y s^-1}
            nA &= ~seenA
            seenB |= nB
            seenA |= nA
            fA = np.flatnonzero(nA)
            fB = np.flatnonzero(nB)
        total += 2 * N - int(seenA.sum()) - int(seenB.sum())
    return total


def _climb(N, Tc, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S (identity fixed in S) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, Tc, invs, S, D)
    temp = 2.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(N, Tc, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i] = old
        temp = max(0.25, temp * 0.999)
    return list(S) if cur == 0 else None


def _probe(d, D, N, rng, deadline):
    """Try to find a valid bi-Cayley lift on 2N vertices before the deadline; else None."""
    if N < d:
        return None
    groups = _groups(N)
    if not groups:
        return None
    rng.shuffle(groups)
    # Non-abelian groups first: abelian (cyclic / direct product) lifts stall earlier.
    groups.sort(key=lambda g: g[0] == 1 or g[2] == 1)
    groups = groups[:10]
    tables = []
    for m, k, r in groups:
        if time.monotonic() > deadline:
            break
        _, Tc, invs = _table(m, k, r)
        tables.append((Tc, invs))
    for _ in range(3):
        for Tc, invs in tables:
            if time.monotonic() > deadline:
                return None
            S = _climb(N, Tc, invs, d, D, rng, 1000, deadline)
            if S is not None:
                edges = []
                for s in S:
                    col = Tc[s].tolist()
                    edges.extend((x, N + col[x]) for x in range(N))
                n = 2 * N
                if lib.is_valid(n, edges, d, D):
                    return n, edges
    return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 40), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
        return best

    moore = lib.moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    if best[0] >= moore or d < 2:
        return best

    # Bisection on the group order N (graph has 2N vertices).
    # lo: a known order that is at least as good; hi: order assumed infeasible.
    lo = best[0] // 2
    hi = moore // 2 + 1
    while hi - lo > 1 and time.monotonic() < deadline:
        mid = (lo + hi) // 2
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, 0.25 * (deadline - now)))
        res = _probe(d, D, mid, rng, slice_end)
        if res is not None:
            if res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res
            lo = mid
        else:
            hi = mid

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
