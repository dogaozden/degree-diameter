import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bipartite bi-Cayley graphs over small semidirect products Z_m x| Z_k.
#
# Group G = Z_m x| Z_k with (a, b) * (c, e) = (a + r^b c, b + e), coded a*k + b.
# Vertices: A_g = g and B_h = G + h. For a connection set S of d distinct group
# elements, A_g is joined to B_{g s} for every s in S. Left multiplication is an
# automorphism that preserves both sides, so the diameter is certified by BFS from
# A_e and from B_e only. Each evaluation is a few numpy operations per level.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            try:
                return lib.projective_plane_incidence(q)
            except Exception:
                return None
    return None


def _sample_group(G, rng):
    """Return (m, k, r) with m * k = G, preferring non-abelian semidirect products."""
    ks = [k for k in range(2, G + 1) if G % k == 0 and G // k >= 2]
    if ks and rng.random() < 0.9:
        k = rng.choice(ks)
        m = G // k
        for _ in range(80):
            r = rng.randrange(1, m)
            if r != 1 and math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                return m, k, r
    return G, 1, 1


def _group_maps(m, k, r):
    """Return (G, get) where get(s) = (col, inv) for right multiplication by s."""
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    g = np.arange(G, dtype=np.int64)
    a = g // k
    b = g % k
    base = pw[b]
    cache = {}

    def get(s):
        v = cache.get(s)
        if v is None:
            c = s // k
            dd = s % k
            col = ((a + base * c) % m) * k + (b + dd) % k
            inv = np.empty(G, dtype=np.int64)
            inv[col] = g
            v = (col, inv)
            cache[s] = v
        return v

    return G, get


def _unreached(G, D, cs, start_a):
    """Number of the 2G vertices at distance > D from A_e (start_a) or B_e (not start_a)."""
    vis_a = np.zeros(G, dtype=bool)
    vis_b = np.zeros(G, dtype=bool)
    if start_a:
        vis_a[0] = True
        fr = np.array([0], dtype=np.int64)
        side = 0
    else:
        vis_b[0] = True
        fr = np.array([0], dtype=np.int64)
        side = 1
    for _ in range(D):
        if fr.size == 0:
            break
        if side == 0:
            nb = np.zeros(G, dtype=bool)
            for col, _inv in cs:
                nb[col[fr]] = True
            nb &= ~vis_b
            vis_b |= nb
            fr = np.flatnonzero(nb)
            side = 1
        else:
            na = np.zeros(G, dtype=bool)
            for _col, inv in cs:
                na[inv[fr]] = True
            na &= ~vis_a
            vis_a |= na
            fr = np.flatnonzero(na)
            side = 0
    return 2 * G - int(vis_a.sum()) - int(vis_b.sum())


def _cost(G, D, S, get):
    """Zero exactly when the bi-Cayley graph has diameter <= D."""
    cs = [get(s) for s in S]
    return _unreached(G, D, cs, True) + _unreached(G, D, cs, False)


def _anneal(G, d, D, get, rng, deadline):
    """Simulated annealing over connection sets S. Returns S with cost 0, or None."""
    S = rng.sample(range(G), d)
    cur = _cost(G, D, S, get)
    T = 1.0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        t = rng.randrange(G)
        if t in S:
            continue
        T2 = S[:]
        T2[i] = t
        c2 = _cost(G, D, T2, get)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = T2, c2
        T = max(0.2, T * 0.998)
    return S if cur == 0 else None


def _edges(G, S, get):
    """Full graph for connection set S: 2G vertices, A_g = g, B_h = G + h."""
    E = []
    for s in S:
        col = get(s)[0]
        for g, h in enumerate(col.tolist()):
            E.append((g, G + h))
    return 2 * G, E


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 5.0))
    deadline = t0 + budget

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2, valid for D >= 2).
    best_n, best_e = lib.haar_graph(d, range(d))
    best_e = list(best_e)

    mb = lib.moore_bound(d, D)
    if best_n >= mb:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if best_n >= mb:
                return best_n, best_e

    rng = random.Random(seed * 1000003 + d * 101 + D)

    # Ladder: always search for a bi-Cayley graph one order larger than the best so far.
    while time.monotonic() < deadline:
        G = best_n // 2 + 1
        if 2 * G > mb or G < d:
            break
        m, k, r = _sample_group(G, rng)
        Gn, get = _group_maps(m, k, r)
        att_deadline = min(deadline, time.monotonic() + 2.5)
        S = _anneal(Gn, d, D, get, rng, att_deadline)
        if S is not None:
            n, e = _edges(Gn, S, get)
            consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        best = lib.haar_graph(d, range(d))
        return best[0], list(best[1])
    return best_n, best_e
