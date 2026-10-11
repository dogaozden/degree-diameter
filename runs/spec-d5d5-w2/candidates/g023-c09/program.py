import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Engine: voltage lifts of small base graphs over semidirect products
# Z_m x|_r Z_k, searched by simulated annealing. Every candidate is scored
# exactly on all vertices at once, using bit-parallel reachability in numpy.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)
_TABLES = {}
ITERS = 3000


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _tables(m, k, r):
    """Cached (order, Tm, invs): Tm[x, y] = x*y and invs[g] = g^-1 in Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLES.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    Tm = np.array([[mul(x, y) for y in range(order)] for x in range(order)], dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    if len(_TABLES) >= 64:
        _TABLES.clear()
    _TABLES[key] = (order, Tm, invs)
    return _TABLES[key]


def _lift_nbr(kb, G, Tm, invs, P, S):
    """Neighbour array (V x d) of the layered lift.

    Layer L pairs A_{i,g} with B_{P[L,i], g*S[L,i]}. Each layer is a perfect
    matching between the two sides, so the lift is d-regular.
    """
    d = P.shape[0]
    V = 2 * kb * G
    nbr = np.empty((V, d), dtype=np.int64)
    idx = np.arange(G)
    for L in range(d):
        Pinv = np.empty(kb, dtype=np.int64)
        Pinv[P[L]] = np.arange(kb)
        for i in range(kb):
            nbr[i * G:(i + 1) * G, L] = kb * G + int(P[L, i]) * G + Tm[idx, int(S[L, i])]
        for j in range(kb):
            i = int(Pinv[j])
            nbr[kb * G + j * G: kb * G + (j + 1) * G, L] = i * G + Tm[idx, invs[int(S[L, i])]]
    return nbr


def _base_bits(V):
    """Reachability bitmasks: row v has only bit v set."""
    W = (V + 63) // 64
    base = np.zeros((V, W), dtype=np.uint64)
    v = np.arange(V)
    base[v, v >> 6] = np.uint64(1) << (v & 63).astype(np.uint64)
    return base


def _cost(nbr, base, D, V):
    """Number of ordered vertex pairs at distance more than D. Zero means valid."""
    reach = base
    for _ in range(D):
        reach = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
    got = int(_POP8[reach.view(np.uint8)].sum())
    return V * V - got


def _search(d, D, kb, G, Tm, invs, rng, deadline, iters):
    """Anneal voltages (and layer permutations when kb > 1) to zero bad pairs."""
    V = 2 * kb * G
    base = _base_bits(V)

    def cost_of(P, S):
        nbr = _lift_nbr(kb, G, Tm, invs, P, S)
        srt = np.sort(nbr, axis=1)
        if np.any(srt[:, 1:] == srt[:, :-1]):   # multi-edge: reject
            return V * V
        return _cost(nbr, base, D, V)

    P = np.array([rng.sample(range(kb), kb) for _ in range(d)], dtype=np.int64)
    S = np.array([[rng.randrange(G) for _ in range(kb)] for _ in range(d)], dtype=np.int64)
    if kb == 1:
        S[0, 0] = 0  # identity WLOG for bi-Cayley graphs
    cost = cost_of(P, S)
    T = max(1.0, 0.02 * cost)
    Tend = 0.2
    decay = (Tend / T) ** (1.0 / iters) if T > Tend else 1.0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T *= decay
        P2 = P.copy()
        S2 = S.copy()
        if kb == 1 or rng.random() < 0.7:
            L = rng.randrange(1 if kb == 1 else 0, d)
            S2[L, rng.randrange(kb)] = rng.randrange(G)
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(kb), 2)
            P2[L, a], P2[L, b] = P2[L, b], P2[L, a]
        c2 = cost_of(P2, S2)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            P, S, cost = P2, S2, c2

    if cost != 0:
        return None
    nbr = _lift_nbr(kb, G, Tm, invs, P, S)
    return [(v, int(b)) for v in range(kb * G) for b in nbr[v]]


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
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: ladder upward from the current best order.
    while best_n < moore and time.monotonic() < deadline:
        kb = rng.choice((1, 1, 1, 2, 2, 3))
        lo = best_n // (2 * kb) + 1
        if 2 * kb * lo > moore:
            kb = 1
            lo = best_n // 2 + 1
            if 2 * lo > moore:
                break
        N = lo + rng.randrange(4)
        groups = _groups(N)
        if not groups:
            continue
        m, k2, r = rng.choice(groups)
        order, Tm, invs = _tables(m, k2, r)
        edges = _search(d, D, kb, order, Tm, invs, rng, deadline, ITERS)
        if edges is not None:
            consider(2 * kb * order, edges)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
