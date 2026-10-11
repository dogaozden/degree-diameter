import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact baseline: incidence graph of PG(2, q) (diameter 3).
# ----------------------------------------------------------------------------

def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q capped for speed)."""
    for q in range(min(d - 1, 13), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: single-block bi-Cayley graphs B(G, S).
#
# Vertices: A_g = g (0 <= g < G) and B_h = G + h. Edge A_g ~ B_{g*s} for s in S,
# where G is a semidirect product Z_m x| Z_k (or cyclic). The graph is d-regular
# and bipartite. Left multiplication is an automorphism that acts transitively on
# each side, so diameter <= D reduces to two BFS runs, one from A_identity and one
# from B_identity. The connection set S (|S| = d) is found by simulated annealing
# on the number of vertices left unreached within distance D.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (m, k, r) describing Z_m x| Z_k of order G = m*k with r^k = 1 mod m, gcd(r, m) = 1."""
    divs = [k for k in range(1, G + 1) if G % k == 0]
    k = rng.choice(divs)
    m = G // k
    if m == 1 or k == 1:
        return (m, k, 0)
    for _ in range(80):
        r = rng.randrange(1, m)
        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
            return (m, k, r)
    return (m, k, 1)  # r = 1 always gives the cyclic group Z_m x Z_k


def _group_tables(m, k, r):
    """Return (G, M, Inv): M[x, y] = x*y and Inv[s] = s^{-1}, with identity index 0."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    if m > 1:
        pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    else:
        pw = np.zeros(k, dtype=np.int64)
    M = ((a[:, None] + pw[b[:, None]] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    Inv = (M == 0).argmax(axis=0).astype(np.int64)
    return G, M, Inv


def _unreached(adj, G, D):
    """Count vertices not reached within D steps from A_identity and from B_identity."""
    total = 0
    N = 2 * G
    for src in (0, G):
        vis = np.zeros(N, dtype=bool)
        vis[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[front].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            front = nb
        total += N - int(vis.sum())
    return total


def _cost(S, G, M, Inv, D):
    Sarr = np.array(S, dtype=np.int64)
    invS = Inv[Sarr]
    adj = np.empty((2 * G, len(S)), dtype=np.int64)
    adj[:G] = G + M[:, Sarr]
    adj[G:] = M[:, invS]
    return _unreached(adj, G, D)


def _anneal(d, D, G, M, Inv, rng, t_end):
    """Anneal a connection set S of size d; return S with zero defect, or None."""
    if G < d:
        return None
    S = rng.sample(range(G), d)
    c = _cost(S, G, M, Inv, D)
    while c > 0 and time.monotonic() < t_end:
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        S2 = list(S)
        S2[i] = new
        c2 = _cost(S2, G, M, Inv, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / 1.0):
            S, c = S2, c2
    return S if c == 0 else None


def _bicayley_edges(G, M, S):
    return [(g, G + int(M[g, s])) for g in range(G) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D >= 3:
        pg = _pg_baseline(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley search: grow the group order G, so the graph has 2G vertices.
    try:
        bound = lib.moore_bound(d, D)
        bestG = best_n // 2
        step = max(1, bestG // 20)
        while time.monotonic() < deadline:
            G = bestG + step
            if 2 * G > bound:
                break
            found = None
            for _ in range(4):
                now = time.monotonic()
                if now >= deadline:
                    break
                slice_len = max(0.5, min(3.0, (deadline - now) / 4.0))
                m, k, r = _sample_group(G, rng)
                Gg, M, Inv = _group_tables(m, k, r)
                S = _anneal(d, D, Gg, M, Inv, rng, min(deadline, now + slice_len))
                if S is not None:
                    found = (Gg, M, S)
                    break
            if found is not None:
                Gg, M, S = found
                before = best_n
                consider(2 * Gg, _bicayley_edges(Gg, M, S))
                if best_n > before:
                    bestG = best_n // 2
                    step = max(step, 1)
                else:
                    step = max(1, step // 2)
            else:
                step = max(1, step // 2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
