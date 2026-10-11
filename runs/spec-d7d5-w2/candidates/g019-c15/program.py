import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective-plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW construction: Haar graphs of finite groups.
#
# For a group G and a d-subset S of G, the Haar graph H(G, S) has vertices
# a_g and b_h (g, h in G) with a_g ~ b_{g s} for s in S. It is d-regular and
# bipartite, with 2|G| vertices. Left multiplication is an automorphism
# that preserves both sides, so the diameter is at most D exactly when the
# BFS balls from a_e and b_e both cover the whole graph within D steps.
# That makes each evaluation cheap, and the search runs over S and over
# non-abelian groups Z_m x| Z_k of the target order.
# ----------------------------------------------------------------------------

def _group_table(G, k, r):
    """Multiplication table M (G x G) and inverse array for Z_m x| Z_k, m = G // k.

    Element (a, b) is coded as a*k + b; (a, b)(c, e) = (a + r^b c, b + e).
    The identity is index 0.
    """
    m = G // k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(M == 0)
    inv[rows] = cols
    return M, inv


def _draw_group(G, rng):
    """Random group of order G as Z_m x| Z_k, with a random multiplication table."""
    divs = [k for k in range(1, G + 1) if G % k == 0]
    k = rng.choice(divs)
    m = G // k
    r = 1
    if m > 2 and k > 1 and rng.random() < 0.7:
        for _ in range(60):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                r = c
                break
    return _group_table(G, k, r)


def _uncovered(M, S, invS, G, D, src):
    """Number of vertices NOT within distance D of the source vertex (ids: A g -> g, B h -> G + h)."""
    dist = np.full(2 * G, -1, dtype=np.int64)
    dist[src] = 0
    frontier = np.array([src], dtype=np.int64)
    for lev in range(1, D + 1):
        parts = []
        fa = frontier[frontier < G]
        fb = frontier[frontier >= G] - G
        if fa.size:
            # a_g ~ b_{g s}
            parts.append(M[fa[:, None], S[None, :]].ravel() + G)
        if fb.size:
            # b_h ~ a_{h s^{-1}}
            parts.append(M[fb[:, None], invS[None, :]].ravel())
        if not parts:
            break
        c = np.concatenate(parts)
        c = np.unique(c[dist[c] < 0])
        if c.size == 0:
            break
        dist[c] = lev
        frontier = c
    return int(np.count_nonzero(dist < 0))


def _score(M, inv, S, G, D):
    """Total uncovered count from a_e and b_e; zero means the diameter is at most D."""
    invS = inv[S]
    return _uncovered(M, S, invS, G, D, 0) + _uncovered(M, S, invS, G, D, G)


def _haar_edges(G, M, S):
    """Edge list of H(G, S): a_g (id g) joined to b_{g s} (id G + g s)."""
    d = len(S)
    A = np.repeat(np.arange(G, dtype=np.int64), d)
    B = G + M[:, S].ravel()
    return list(zip(A.tolist(), B.tolist()))


def _attempt(G, d, D, rng, t_end):
    """Hill-climb over connection sets S for random groups of order G. Returns edges or None."""
    while time.monotonic() < t_end:
        M, inv = _draw_group(G, rng)
        S = rng.sample(range(G), d)
        S_arr = np.array(S, dtype=np.int64)
        cur = _score(M, inv, S_arr, G, D)
        stall = 0
        while cur > 0 and stall < 1500 and time.monotonic() < t_end:
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                stall += 1
                continue
            S2 = S_arr.copy()
            S2[i] = x
            sc = _score(M, inv, S2, G, D)
            if sc <= cur:
                if sc < cur:
                    stall = 0
                else:
                    stall += 1
                S, S_arr, cur = S[:i] + [x] + S[i + 1:], S2, sc
            else:
                stall += 1
        if cur == 0:
            return _haar_edges(G, M, S_arr)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))

    if d < 1 or D < 0:
        return 1, []
    if D == 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    rng = random.Random(seed)
    moore = lib.moore_bound(d, D)
    cap_G = max(d, moore // 2)

    best_G = max(d, best[0] // 2)
    total = max(1e-3, deadline - start)
    inc = max(1, best_G // 50)

    # Grow the group order by search; adapt the step size on success or failure.
    while time.monotonic() < deadline and best_G < cap_G:
        G = min(best_G + inc, cap_G)
        if G <= best_G:
            break
        now = time.monotonic()
        t_end = now + min(deadline - now, max(1.5, 0.12 * total))
        edges = _attempt(G, d, D, rng, t_end)
        if edges is not None:
            n = 2 * G
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_G = G
                inc = min(inc * 2, max(1, best_G // 10))
            else:
                inc = max(1, inc // 2)
        else:
            inc = max(1, inc // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        if not lib.is_valid(best[0], best[1], d, D):
            return 1, []
    return best
