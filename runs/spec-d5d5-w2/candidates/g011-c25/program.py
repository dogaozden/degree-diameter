import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Vectorised bi-Cayley search.
#
# A bi-Cayley graph over a group G of order N has vertices A_x and B_x (x in G)
# and edges A_x ~ B_{x*g} for g in S, |S| = d. Left translation is an
# automorphism, so the diameter check only needs BFS from A_0 and B_0.
#
# Unlike the earlier pure-Python climb, the BFS here works on numpy index
# arrays: each level is one fancy-index gather plus a unique(). Simulated
# annealing (not a plain hill climb) moves one connection element at a time,
# with cost = number of vertex pairs farther than D from the two sources.
# Groups are semidirect products Z_m x|_r Z_k, which include cyclic and
# dihedral groups.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # groups tried per order N before moving on
ANNEAL_ITERS = 2500   # annealing steps per (N, group)
N_WINDOW = 8          # candidate orders above the current lower bound
SLICE_SECONDS = 5.0   # wall time allowed per order-N attempt
_TABLE_CACHE = {}


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
    """(order, T, invs): T[x, g] = x*g as an int array, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(order)] for x in range(order)],
                 dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _adjacency(N, T, invs, S):
    """Neighbour index array of shape (2N, d): row x is A_x, row N+y is B_y."""
    S = np.asarray(S, dtype=np.int64)
    adjA = N + T[:, S]          # A_x ~ B_{x g}
    adjB = T[:, invs[S]]        # B_y ~ A_{y g^-1}
    return np.vstack([adjA, adjB])


def _unreached(N, adj, D):
    """Number of vertex pairs (source, target) not within distance D, sources A_0 and B_0."""
    total = 0
    for s in (0, N):
        seen = np.zeros(2 * N, dtype=bool)
        seen[s] = True
        frontier = np.array([s], dtype=np.int64)
        count = 1
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            count += int(nb.size)
            frontier = nb
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S (identity fixed as element 0, WLOG).

    Returns S with zero unreached pairs, or None.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, _adjacency(N, T, invs, S), D)
    if cur == 0:
        return S
    T0 = 0.02 * cur + 1.0
    for it in range(iters):
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        frac = it / iters
        temp = T0 * (1.0 - frac) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(N, _adjacency(N, T, invs, S), D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = v
            if cur == 0:
                return S
        else:
            S[i] = old
    return None


def _edges_from(N, T, S):
    return [(x, N + int(T[x, g])) for x in range(N) for g in S]


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
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, order 2d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3: projective plane incidence graph when a prime power q = d-1 exists
    # (or the largest one below it).
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n0, e0 = lib.projective_plane_incidence(q)
                consider(n0, e0)
                break

    try:
        while best[0] < moore and time.monotonic() < deadline:
            lo = best[0] // 2 + 1
            N = lo + rng.randrange(N_WINDOW)
            if 2 * N > moore:
                break
            slice_end = min(deadline, time.monotonic() + SLICE_SECONDS)
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k, r in groups[:MAX_GROUPS]:
                if time.monotonic() > slice_end:
                    break
                order, T, invs = _table(m, k, r)
                S = _anneal(N, T, invs, d, D, rng, slice_end, ANNEAL_ITERS)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                consider(2 * N, _edges_from(N, T, S))
    except Exception:
        pass  # keep whatever valid graph we already have

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
