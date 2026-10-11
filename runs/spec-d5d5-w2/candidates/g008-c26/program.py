import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Vectorised voltage-lift search.
#
# A k-base lift over a group G has vertices A_{i,x} = i*G + x and
# B_{j,y} = (k+j)*G + y. Each of the d layers L carries a permutation p_L of
# the k base vertices and a voltage s_L in G, giving edges
# A_{i,x} ~ B_{p_L(i), x*s_L}. The lift is d-regular and bipartite.
#
# Left translation by G is an automorphism, so it suffices to check
# eccentricities from the 2k base representatives. Each BFS level is a single
# numpy fancy-index step over a precomputed neighbour array. Simulated
# annealing minimises the number of unreached (source, vertex) pairs.
# ----------------------------------------------------------------------------

_TABLES = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving groups Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached multiplication table M[x, g] = x*g and inverse array for the group."""
    key = (m, k, r)
    hit = _TABLES.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    M = np.array([[mul(x, g) for g in range(order)] for x in range(order)],
                 dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    if len(_TABLES) >= 32:
        _TABLES.clear()
    _TABLES[key] = (M, invs)
    return M, invs


def _build_nbr(d, k, G, M, invs, s, p):
    """Neighbour array of shape (2kG, d): column L is the layer-L neighbour."""
    V = 2 * k * G
    nbr = np.empty((V, d), dtype=np.int64)
    for L in range(d):
        colA = M[:, s[L]]
        colB = M[:, invs[s[L]]]
        for i in range(k):
            j = p[L][i]
            nbr[i * G:(i + 1) * G, L] = (k + j) * G + colA
            nbr[(k + j) * G:(k + j + 1) * G, L] = i * G + colB
    return nbr


def _cost(k, G, D, nbr):
    """Total number of (base representative, vertex) pairs not within distance D."""
    V = 2 * k * G
    total = 0
    for b in range(2 * k):
        src = b * G
        vis = np.zeros(V, dtype=bool)
        vis[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = np.zeros(V, dtype=bool)
            nb[nbr[fr].ravel()] = True
            nb &= ~vis
            if not nb.any():
                break
            vis |= nb
            fr = np.flatnonzero(nb)
        total += V - int(vis.sum())
    return total


def _anneal(d, D, k, G, M, invs, rng, deadline, iters):
    """Anneal voltages and layer permutations. Returns (n, edges) if a valid lift is found."""
    s = [rng.randrange(G) for _ in range(d)]
    if k == 1:
        s[0] = 0  # WLOG for k = 1: relabelling makes the identity a connection element
    p = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        p.append(perm)

    nbr = _build_nbr(d, k, G, M, invs, s, p)
    cur = _cost(k, G, D, nbr)
    T0 = 2.0 + 0.05 * cur

    for step in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        L = rng.randrange(d)
        old_s, old_p = s[L], p[L]
        if k == 1 or rng.random() < 0.6:
            if k == 1 and L == 0:
                continue
            ns = rng.randrange(G)
            if ns == old_s:
                continue
            s[L] = ns
        else:
            a, b = rng.sample(range(k), 2)
            np_ = list(old_p)
            np_[a], np_[b] = np_[b], np_[a]
            p[L] = np_
        nbr2 = _build_nbr(d, k, G, M, invs, s, p)
        c2 = _cost(k, G, D, nbr2)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = c2
            nbr = nbr2
        else:
            s[L], p[L] = old_s, old_p

    if cur != 0:
        return None
    edges = set()
    for L in range(d):
        for i in range(k):
            j = p[L][i]
            for x in range(G):
                u = i * G + x
                v = (k + j) * G + int(M[x, s[L]])
                edges.add((u, v))
    return 2 * k * G, sorted((int(u), int(v)) for u, v in edges)


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
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                if lib.is_valid(n, e, d, D):
                    best = (n, e)
                break
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Search: voltage lifts with k base vertices per side, k in {1, 2, 3}.
    # Targets are half-orders h = k*G, so the total order is 2h. The window
    # starts just above the current best and is swept least-tried first.
    tried = {}
    MAX_GROUPS = 4
    ITERS = 2500
    while time.monotonic() < deadline:
        n_best = best[0]
        if n_best >= moore:
            break
        h_lo = n_best // 2 + 1
        h_hi = min(h_lo + max(2, h_lo // 10), moore // 2 + 1)
        if h_hi <= h_lo:
            break
        h = min(range(h_lo, h_hi), key=lambda x: (tried.get(x, 0), rng.random()))
        tried[h] = tried.get(h, 0) + 1

        ks = [k for k in (1, 2, 3) if h % k == 0]
        k = rng.choice(ks)
        G = h // k
        if G < 1:
            continue

        groups = _groups(G)
        rng.shuffle(groups)
        for m, k2, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            M, invs = _tables(m, k2, r)
            res = _anneal(d, D, k, G, M, invs, rng, deadline, ITERS)
            if res is not None:
                consider(res[0], res[1])
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
