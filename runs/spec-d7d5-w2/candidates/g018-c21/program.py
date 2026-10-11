import functools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Construction: bipartite voltage lifts over semidirect products Z_m x| Z_k2.
#
# Base: k "A-blocks" and k "B-blocks", each a copy of a group G (|G| = m*k2).
# Layer l (for l < d) is a bijection sig_l from A-blocks to B-blocks with a
# voltage s_{l,i} in G. A-vertex (i,g) is joined to B-vertex (sig_l(i), g*s_{l,i})
# for every layer l. Every vertex gets exactly d neighbours (if no duplicates).
#
# Left multiplication by G is an automorphism that preserves blocks, so the
# diameter condition reduces to BFS from one representative per block:
# 2k sources instead of all vertices. The search minimises the number of
# unreached (source, vertex) pairs plus a penalty for duplicate edges, by
# simulated annealing over voltages and block permutations.
#
# Safe fallback: K_{d,d} (diameter 2). Projective-plane incidence graphs are
# used when they apply. Every candidate is checked with lib.is_valid.
# ----------------------------------------------------------------------------

_PEN = 50


@functools.lru_cache(maxsize=None)
def _group_choices(G):
    """Return (m, k2, r) triples for Z_m x| Z_k2 of order G (r = 1 for the direct product)."""
    out = [(G, 1, 1)]  # cyclic group
    for k2 in range(2, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return tuple(out)


def _group_table(m, k2, r):
    """Return (G, M, inv): M[x, y] = x*y, inv[x] = x^{-1}, identity = 0."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    inv = np.empty(G, dtype=np.int64)
    pairs = np.argwhere(M == 0)
    inv[pairs[:, 0]] = pairs[:, 1]
    return G, M, inv


def _build_nbr(k, d, G, M, inv, sig, volt):
    """Neighbour table (N x d). A-block i is rows i*G.., B-block j is rows (k+j)*G..."""
    N = 2 * k * G
    nbr = np.empty((N, d), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            j = sig[l][i]
            s = volt[l][i]
            nbr[i * G:(i + 1) * G, l] = (k + j) * G + M[:, s]
            nbr[(k + j) * G:(k + j + 1) * G, l] = i * G + M[:, inv[s]]
    return nbr


def _cost(k, d, G, D, nbr):
    """Unreached (source, vertex) pairs after D steps, plus penalty for duplicate edges."""
    N = nbr.shape[0]
    S = 2 * k
    R = np.zeros((S, N), dtype=bool)
    R[np.arange(S), np.arange(S) * G] = True
    for _ in range(D):
        new = R.copy()
        for l in range(d):
            new |= R[:, nbr[:, l]]
        if np.array_equal(new, R):
            break
        R = new
    unreached = S * N - int(R.sum())
    srt = np.sort(nbr, axis=1)
    dups = int((srt[:, 1:] == srt[:, :-1]).sum())
    return unreached + _PEN * dups


def _anneal(k, d, D, G, M, inv, rng, deadline, iters):
    """Simulated annealing over voltages and block permutations. Returns nbr table or None."""
    sig = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = _build_nbr(k, d, G, M, inv, sig, volt)
    cost = _cost(k, d, G, D, nbr)
    for t in range(iters):
        if cost == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        temp = 0.4 + 2.0 * (1.0 - t / iters)
        l = rng.randrange(d)
        if k >= 2 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(k), 2)
            sig[l][i1], sig[l][i2] = sig[l][i2], sig[l][i1]
            nb = _build_nbr(k, d, G, M, inv, sig, volt)
            c2 = _cost(k, d, G, D, nb)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                nbr, cost = nb, c2
            else:
                sig[l][i1], sig[l][i2] = sig[l][i2], sig[l][i1]
        else:
            i = rng.randrange(k)
            old = volt[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volt[l][i] = new
            nb = _build_nbr(k, d, G, M, inv, sig, volt)
            c2 = _cost(k, d, G, D, nb)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                nbr, cost = nb, c2
            else:
                volt[l][i] = old
    if cost != 0:
        return None
    return nbr


def _nbr_to_edges(nbr):
    """Edges (A-vertex, B-vertex); A indices are always smaller than B indices."""
    edges = []
    for v in range(nbr.shape[0]):
        for u in nbr[v]:
            u = int(u)
            if v < u:
                edges.append((v, u))
    return edges


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _pg_candidate(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    # Lift search with a small bandit-free random mix over block counts.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 2, 2, 3])
        G_target = best_n // (2 * k) + 1 + rng.randrange(0, 3)
        if G_target > 2000:
            continue
        choices = _group_choices(G_target)
        if not choices:
            continue
        m, k2, r = rng.choice(choices)
        G, M, inv = _group_table(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        nbr = _anneal(k, d, D, G, M, inv, rng, deadline, 2500)
        if nbr is not None:
            consider(2 * k * G, _nbr_to_edges(nbr))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
