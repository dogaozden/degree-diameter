import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: PG(2, q) incidence graphs (diameter 3, valid for any D >= 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: bi-Cayley graphs over finite groups G = Z_m x| Z_k2.
#
# Vertices: side 0 is g (0 <= g < G), side 1 is G + h.
# Connection set S (d distinct group elements): (g, side 0) ~ (g*s, side 1).
# Every vertex has degree exactly d, and the graph is bipartite and simple.
#
# Because left multiplication is an automorphism, the diameter condition reduces to
# two BFS runs, from (e,0) and from (e,1), with walks alternating sides. Each run must
# reach every vertex on both sides within D steps. The cost is the number of
# uncovered (start, target) pairs, so the search is fast and fully vectorised.
# ----------------------------------------------------------------------------

def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs). Ts[s, g] = g*s and Invs[s, h] = h*s^{-1}, for Z_m x| Z_k2."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    pw = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    Invs[np.arange(G)[:, None], Ts] = x[None, :]  # Invs[s, g*s] = g
    return G, Ts, Invs


def _sample_group(G, rng):
    """Return (m, k2, r) with m*k2 = G, m >= 2, and a valid semidirect r (r = 1 is always valid)."""
    cands = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not cands:
        return None
    if rng.random() < 0.5:
        k2 = 1
    else:
        k2 = rng.choice(cands)
    m = G // k2
    if k2 == 1:
        return m, 1, 1
    for _ in range(40):
        r = rng.randrange(1, m)
        if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
            return m, k2, r
    return m, k2, 1  # abelian fallback, always valid


def _cost(S, G, Ts, Invs, D):
    """Total uncovered (start, target) pairs over both starting sides, within distance D."""
    total = 0
    for a in (0, 1):
        R = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        cur = np.zeros(G, dtype=bool)
        cur[0] = True
        R[a] |= cur
        side = a
        for _ in range(D):
            tab = Ts if side == 0 else Invs
            nxt = np.zeros(G, dtype=bool)
            for s in S:
                nxt[tab[s]] |= cur
            side ^= 1
            R[side] |= nxt
            cur = nxt
            if R[0].all() and R[1].all():
                break
        total += G - int(R[0].sum()) + G - int(R[1].sum())
    return total


def _anneal(G, Ts, Invs, d, D, rng, iters, deadline):
    """Local search over d-element connection sets. Returns a list S with zero cost, or None."""
    if d > G:
        return None
    S = rng.sample(range(G), d)
    cost = _cost(S, G, Ts, Invs, D)
    for t in range(iters):
        if cost == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        temp = 1.0 + 2.0 * (1.0 - t / iters)
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _cost(S, G, Ts, Invs, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[i] = old
    return S if cost == 0 else None


def _bicayley_edges(G, Ts, S):
    """Edges of the bi-Cayley graph: side-0 g joined to side-1 G + g*s for s in S."""
    return [(g, G + t) for s in S for g, t in enumerate(Ts[s].tolist())]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d >= 2:
        per_attempt = max(0.5, 0.04 * budget)
        fails = 0
        while time.monotonic() < deadline - 0.2:
            half = best_n // 2
            spread = min(4, fails // 4)
            G = max(d + 1, half + 1 + rng.randrange(0, spread + 1))
            grp = _sample_group(G, rng)
            if grp is None:
                fails += 1
                continue
            m, k2, r = grp
            G2, Ts, Invs = _semidirect_tables(m, k2, r)
            att_deadline = min(deadline, time.monotonic() + per_attempt)
            S = _anneal(G2, Ts, Invs, d, D, rng, 4000, att_deadline)
            if S is not None:
                n2 = 2 * G2
                e2 = _bicayley_edges(G2, Ts, S)
                if n2 > best_n and lib.is_valid(n2, e2, d, D):
                    best = (n2, e2)
                    best_n = n2
                    fails = 0
                    continue
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
