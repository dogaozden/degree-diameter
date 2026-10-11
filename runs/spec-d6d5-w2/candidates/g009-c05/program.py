import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _baseline(d, D):
    """Always-valid fallback: K_{d,d} (diameter 2), or a single edge when D = 1."""
    if d < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# New family: bi-Cayley graphs (Haar-type) over non-abelian groups.
#
# Vertices a_g = g (side A) and b_h = G + h (side B), G = |group|.
# Connection set S = {s_1..s_d} of distinct group elements: a_g ~ b_{g*s_i}.
# Left multiplication is an automorphism, so the graph is vertex-transitive
# on each side. The diameter test therefore needs only two BFS runs, one from
# a_e and one from b_e, each of which costs O(d * G).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k of order G (k | G), or None."""
    ks = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not ks:
        return None
    k = rng.choice(ks)
    m = G // k
    if k == 1:
        r = 1
    else:
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            return None
        r = rng.choice(rs)
    return lib.semidirect_group(m, k, r)  # (order, mul, inv)


def _unreached(G, D, R, L, side):
    """Number of vertices (both sides) not reached within D steps from the identity of `side`.

    R[i][g] = g * s_i (neighbours of a_g are b_{R[i][g]}).
    L[i][h] = h * s_i^{-1} (neighbours of b_h are a_{L[i][h]}).
    """
    visA = bytearray(G)
    visB = bytearray(G)
    if side == 0:
        visA[0] = 1
        fa, fb = [0], []
    else:
        visB[0] = 1
        fa, fb = [], [0]
    cnt = 1
    for _ in range(D):
        if not fa and not fb:
            break
        nb = []
        for g in fa:
            for Rp in R:
                h = Rp[g]
                if not visB[h]:
                    visB[h] = 1
                    nb.append(h)
        na = []
        for h in fb:
            for Lp in L:
                g = Lp[h]
                if not visA[g]:
                    visA[g] = 1
                    na.append(g)
        cnt += len(nb) + len(na)
        fa, fb = na, nb
    return 2 * G - cnt


def _search_group(d, D, G, mul, inv, rng, deadline, iters):
    """Anneal a connection set of d distinct elements so the bi-Cayley graph has diameter <= D."""
    S = rng.sample(range(G), d)

    def tables(s):
        si = inv(s)
        return ([mul(g, s) for g in range(G)], [mul(h, si) for h in range(G)])

    tabs = [tables(s) for s in S]

    def cost_of(ts):
        R = [t[0] for t in ts]
        L = [t[1] for t in ts]
        return _unreached(G, D, R, L, 0) + _unreached(G, D, R, L, 1)

    cur = cost_of(tabs)
    T = 2.0
    it = 0
    while cur > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(d)
        s_new = rng.randrange(G)
        if s_new in S:
            continue
        old_t, old_s = tabs[i], S[i]
        tabs[i], S[i] = tables(s_new), s_new
        c = cost_of(tabs)
        T = max(0.1, T * 0.995)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            tabs[i], S[i] = old_t, old_s
    return (list(S) if cur == 0 else None), cur


def _bicayley_edges(G, mul, S):
    return [(g, G + mul(g, s)) for s in S for g in range(G)]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    best = _baseline(d, D)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d >= 1 and D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Bi-Cayley search over non-abelian (semidirect) groups, for D >= 4 (and for D = 3
    # when there is time). Try group orders just above the current best half-order.
    if d >= 2 and D >= 3:
        while time.monotonic() < deadline:
            lo = max(3, best_n // 2 + 1)
            G = rng.randint(lo, lo + max(6, lo // 5))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul, inv = g
            if order < d:
                continue
            S, _ = _search_group(d, D, order, mul, inv, rng, deadline, 600)
            if S is not None:
                consider(2 * order, _bicayley_edges(order, mul, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = _baseline(d, D)
    return best
