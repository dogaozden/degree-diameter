import math
import random
import time

import lib


FRAC_TOTAL = 0.80          # fraction of time_limit we are willing to use
ANNEAL_ITERS = 2500        # annealing steps per attempted group order
ATTEMPT_CAP = 1.5          # seconds per (order, group) attempt, at most


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) graphs over a finite group G of order g.
#
# Vertices: A_x = x (0 <= x < g) and B_y = g + y.
# Connection set S (|S| = d, distinct elements of G).
# Edges: A_x ~ B_{x*s} for every s in S.
#
# Every edge is A-B, so the graph is bipartite, and each vertex has degree d.
# Left multiplication by a group element is an automorphism that preserves
# sides, so the graph has diameter <= D iff the distances from A_e and from
# B_e reach all vertices within D steps.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul, inv) for a random semidirect product Z_m x| Z_k with m*k = G, or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0]
    for _ in range(60):
        k = rng.choice(divs)
        m = G // k
        if k == 1:
            r = 1
        else:
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        if order == G:
            return order, mul, inv
    return None


def _tables(G, mul, inv):
    """Multiplication table T[x][y] = x*y and inverse list I."""
    T = [[mul(x, y) for y in range(G)] for x in range(G)]
    I = [inv(x) for x in range(G)]
    return T, I


def _cost(G, D, S, T, I):
    """Number of (source, vertex) pairs not reached within D steps, for sources A_e and B_e."""
    N = 2 * G
    adj = [None] * N
    for g in range(G):
        Tg = T[g]
        adj[g] = [G + Tg[s] for s in S]
    for h in range(G):
        Th = T[h]
        adj[G + h] = [Th[I[s]] for s in S]
    total = 0
    for src in (0, G):
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _search(G, d, D, rng, deadline, iters):
    """Anneal a connection set S of size d in a random group of order G; return (n, edges) or None."""
    if G < d:
        return None
    grp = _sample_group(G, rng)
    if grp is None:
        return None
    _, mul, inv = grp
    T, I = _tables(G, mul, inv)
    S = rng.sample(range(G), d)
    c = _cost(G, D, S, T, I)
    T0 = 2.0
    T_end = 0.1
    for it in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (T_end / T0) ** (it / max(1, iters))
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cost(G, D, S, T, I)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
        else:
            S[i] = old
    if c != 0:
        return None
    edges = [(g, G + T[g][s]) for g in range(G) for s in S]
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + FRAC_TOTAL * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    moore = lib._moore_bound(d, D)

    # Search group orders G upward from the current best (vertices = 2G).
    lo = max(d, best[0] // 2 + 1)
    fails = 0
    try:
        while time.monotonic() < deadline:
            G = lo + rng.randrange(0, 3)
            if 2 * G > moore:
                break
            now = time.monotonic()
            slice_end = min(deadline, now + ATTEMPT_CAP)
            res = _search(G, d, D, rng, slice_end, ANNEAL_ITERS)
            if res is not None:
                n, e = res
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                    lo = G + 1
                    continue
            fails += 1
            if fails % 3 == 0:
                lo += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
