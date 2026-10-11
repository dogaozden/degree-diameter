import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Directed bi-Cayley (bipartite double of a Cayley digraph) search.
#
# Vertices: A_g = g (side 0) and B_h = G + h (side 1), for g, h in a group of
# order G. Given d distinct darts s_1..s_d, join A_g to B_{g*s} for every g and
# every dart s. Each vertex then has degree d, and the graph is bipartite with
# 2G vertices. Left multiplication is an automorphism, so the diameter test only
# needs BFS from A_e and from B_e: that is O(G d D) work per evaluation.
#
# This differs from the parent's voltage-lift annealing in three ways:
#   * the group multiplication table is built with numpy, not per-call,
#   * the search climbs G one step at a time from the best valid order,
#     so no large group is needed to start,
#   * a cheap cost counts unreached vertices from both side representatives.
# ----------------------------------------------------------------------------

def _sample_table(G, rng):
    """Multiplication table (numpy G x G) of a random group of order G.

    Either the cyclic group Z_G or a semidirect product Z_m x| Z_k (element a*k+b,
    (a,b)*(c,d) = (a + r^b c, b + d)) with r^k = 1 mod m and gcd(r, m) = 1.
    """
    X = np.arange(G, dtype=np.int64)
    ks = [k for k in range(2, min(12, G) + 1) if G % k == 0 and G // k >= 2]
    if ks and rng.random() < 0.7:
        k = rng.choice(ks)
        m = G // k
        units = [r for r in range(1, m) if math.gcd(r, m) == 1]
        if units:
            cands = [r for r in rng.sample(units, min(len(units), 80))
                     if pow(r, k, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
                pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
                a = X // k
                b = X % k
                M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k \
                    + (b[:, None] + b[None, :]) % k
                return M
    return (X[:, None] + X[None, :]) % G


def _cost(G, D, S, Si, Ml):
    """Total number of vertices not reached within D steps from A_e and from B_e."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < G:
                    row = Ml[v]
                    for s in S:
                        w = G + row[s]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = Ml[v - G]
                    for si in Si:
                        w = row[si]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _anneal(G, d, D, Ml, invl, rng, deadline):
    """Anneal the d darts until every vertex is within distance D. Returns darts or None."""
    if d > G:
        return None
    S = rng.sample(range(G), d)
    Si = [invl[s] for s in S]
    cur = _cost(G, D, S, Si, Ml)
    if cur == 0:
        return list(S)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = max(0.02, 1.0 - (now - t0) / span)
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old, old_inv = S[i], Si[i]
        S[i] = x
        Si[i] = invl[x]
        c2 = _cost(G, D, S, Si, Ml)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
            if cur == 0:
                return list(S)
        else:
            S[i] = old
            Si[i] = old_inv


def _edges(G, S, Ml):
    return [(g, G + Ml[g][s]) for g in range(G) for s in S]


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Cheap algebraic families for D >= 3 (diameter 3 each).
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Bold change: climb the order of a directed bi-Cayley graph, one group
    # order at a time, starting from the current best valid graph.
    unit = max(0.5, 0.06 * time_limit)
    best_G = best_n // 2
    step = max(1, best_G // 8)
    fails = 0
    while time.monotonic() < deadline:
        if 2 * best_G >= moore:
            break
        cand = max(best_G + step, d)
        if 2 * cand > moore:
            cand = moore // 2
        if cand <= best_G:
            break

        M = _sample_table(cand, rng)
        Ml = M.tolist()
        invl = np.argmax(M == 0, axis=1).tolist()
        att_end = min(deadline, time.monotonic() + unit)
        S = _anneal(cand, d, D, Ml, invl, rng, att_end)

        if S is not None and consider(2 * cand, _edges(cand, S, Ml)):
            best_G = cand
            step = min(2 * step, max(1, best_G // 8))
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                step = max(1, step // 2)
                fails = 0

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
