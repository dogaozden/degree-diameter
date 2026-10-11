import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Construction used here: bi-Cayley (Haar-type) graphs over a group G.
#
# For a finite group G and a set S of d distinct elements, the graph on
# A_x, B_y (x, y in G) with A_x ~ B_{x*s} for s in S is bipartite, d-regular,
# simple, and has 2|G| vertices. Left multiplication is an automorphism that
# is transitive on each side, so the diameter condition reduces to two
# breadth-first searches, one from A_e and one from B_e.
#
# The search is simulated annealing over the connection set S, with the cost
# equal to the number of vertices unreached within distance D. Groups are
# semidirect products Z_m x| Z_k (k = 1 gives cyclic groups) of order just
# above the current record half-order.
# ----------------------------------------------------------------------------


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(T, rng):
    """Return (m, k, r) describing Z_m x| Z_k with m*k >= T, or None."""
    for _ in range(300):
        k = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12])
        m = max(3, -(-T // k))
        if k == 1:
            return m, 1, 1
        if k == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type, r^2 = 1
            if math.gcd(r, m) == 1 and pow(r, 2, m) == 1 % m:
                return m, k, r
        for _ in range(80):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                return m, k, c
    return None


def _table(m, k, r):
    """Return (G, L) with L[x, y] = x*y in Z_m x| Z_k, element (a, b) coded a*k + b, identity 0."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    L = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return G, L.astype(np.int64)


def _cost(G, L, invt, S, D):
    """Number of (vertex, root) pairs unreached within distance D, for roots A_e and B_e."""
    Sinv = invt[S]

    def bfs(start_a):
        visA = np.zeros(G, dtype=bool)
        visB = np.zeros(G, dtype=bool)
        (visA if start_a else visB)[0] = True
        front = np.array([0], dtype=np.int64)
        side_a = start_a
        for _ in range(D):
            if side_a:
                nxt = L[np.ix_(front, S)].ravel()
                other = visB
            else:
                nxt = L[np.ix_(front, Sinv)].ravel()
                other = visA
            nxt = np.unique(nxt)
            nxt = nxt[~other[nxt]]
            if nxt.size == 0:
                break
            other[nxt] = True
            front = nxt
            side_a = not side_a
        return visA, visB

    vA, vB = bfs(True)
    _, wB = bfs(False)
    return (G - int(vA.sum())) + (G - int(vB.sum())) + (G - int(wB.sum()))


def _anneal(d, D, G, L, invt, rng, deadline, iters):
    """Anneal a connection set S of size d; return the array S on success, else None."""
    S = np.array(rng.sample(range(G), d), dtype=np.int64)
    inS = set(S.tolist())
    cost = _cost(G, L, invt, S, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 3.0 * (1.0 - t / iters))
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in inS:
            continue
        old = int(S[i])
        S[i] = new
        c2 = _cost(G, L, invt, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            inS.discard(old)
            inS.add(new)
            cost = c2
        else:
            S[i] = old
    return S if cost == 0 else None


def _edges_from(G, L, S):
    """Edge list of the bi-Cayley graph: A_x = x, B_y = G + y, A_x ~ B_{x*s}."""
    xs = np.repeat(np.arange(G, dtype=np.int64), len(S))
    ys = L[np.ix_(np.arange(G, dtype=np.int64), S)].ravel() + G
    return list(zip(xs.tolist(), ys.tolist()))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    # Main search: bi-Cayley graphs over groups just above the current record half-order.
    tgt = best_n // 2 + 1
    while time.monotonic() < deadline:
        T = max(tgt, d + 1) + rng.randrange(0, 3)
        g = _sample_group(T, rng)
        if g is None:
            continue
        m, k, r = g
        G, L = _table(m, k, r)
        if G < d or 2 * G <= best_n:
            continue
        invt = np.argmax(L == 0, axis=1)
        attempt_deadline = min(deadline, time.monotonic() + 6.0)
        S = _anneal(d, D, G, L, invt, rng, attempt_deadline, 3000)
        if S is not None:
            consider(2 * G, _edges_from(G, L, S))
            tgt = max(tgt, G + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
