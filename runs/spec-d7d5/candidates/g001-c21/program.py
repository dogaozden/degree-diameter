import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective-plane base (optimal Moore graph when d-1 is a prime power, D = 3).
# ----------------------------------------------------------------------------

def _pg_for(d):
    """Incidence graph of PG(2, q) with q = d - 1 when that is a prime power, else None."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bold family: k = 1 bi-Cayley (Haar-type) graphs over small finite groups.
#
# Group G = Z_m x| Z_k (order G = m*k), elements coded a*k + b.
# Graph: A_g ~ B_{g*s} for every s in a connection set S with |S| = d.
# Left multiplication is an automorphism, so vertex-transitive on each side:
# it suffices that A_e and B_e reach every vertex within distance D.
# Search is over connection sets S (identity kept in S), annealed with a
# numpy BFS cost. This family is different from the k >= 2 voltage lifts
# used by the parent.
# ----------------------------------------------------------------------------

def _sample_table(G, rng):
    """Random semidirect group of order G; return its right-multiplication table tab[g, s] = g*s, or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    k = 1 if rng.random() < 0.4 else rng.choice(divs)
    m = G // k
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    g = np.arange(G, dtype=np.int64)
    a = g // k
    b = g % k
    tab = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    # Each column must be a permutation (so this is a genuine group action).
    if not np.all(np.sort(tab, axis=0) == g[:, None]):
        return None
    return tab


def _cost(tab, S, G, D):
    """Unreached (vertex, representative) pairs from A_e and B_e within distance D. Zero means valid."""
    P = tab[:, S]                      # P[g, s] = g*s  (A -> B)
    Pinv = np.argsort(P, axis=0)       # Pinv[h, s] = g with g*s = h  (B -> A)
    total = 0
    for side0 in (0, 1):
        vis = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        vis[side0][0] = True
        F = vis[side0].copy()
        side = side0
        for _ in range(D):
            if side == 0:
                new = F[Pinv].any(axis=1)   # A-frontier -> B vertices
                tgt = 1
            else:
                new = F[P].any(axis=1)      # B-frontier -> A vertices
                tgt = 0
            new &= ~vis[tgt]
            vis[tgt] |= new
            F = new
            side = tgt
            if not F.any():
                break
        total += 2 * G - int(vis[0].sum()) - int(vis[1].sum())
    return total


def _anneal(tab, G, d, D, rng, deadline, iters):
    """Anneal a connection set S (|S| = d, identity included) to zero cost; return S or None."""
    S = [0] + rng.sample(range(1, G), d - 1)
    cost = _cost(tab, S, G, D)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 2.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()             # in (0, 1]
        limit = cost - T * math.log(u)
        i = rng.randrange(1, d)
        v = rng.randrange(1, G)
        if v in S:
            continue
        T2 = S[:]
        T2[i] = v
        c2 = _cost(tab, T2, G, D)
        if c2 <= limit:
            S, cost = T2, c2
    return S if cost == 0 else None


def _edges(tab, S, G):
    E = []
    for s in S:
        col = tab[:, s].tolist()
        for g in range(G):
            E.append((g, G + col[g]))
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best_n, best_e = fb_n, fb_e
    if D == 2 or d < 3:
        if lib.is_valid(fb_n, fb_e, d, D):
            return fb_n, fb_e
        return 2, [(0, 1)]

    # D = 3 with d-1 a prime power: the projective-plane incidence graph is a Moore graph.
    if D == 3:
        pg = _pg_for(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            return pg[0], pg[1]

    # Main search: k = 1 bi-Cayley graphs over small groups, targeting group orders
    # just above the current best half-order.
    while time.monotonic() < deadline:
        G = best_n // 2 + 1 + rng.randrange(0, max(4, best_n // 60))
        if G < d:
            G = d
        tab = _sample_table(G, rng)
        if tab is None:
            continue
        S = _anneal(tab, G, d, D, rng, deadline, 2500)
        if S is None:
            continue
        n = 2 * G
        edges = _edges(tab, S, G)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best_n, best_e = n, edges

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return fb_n, fb_e
