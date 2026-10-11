"""Bold variant for D >= 3: a different construction family for the weakest case.

The parent searched bi-Cayley voltage lifts with two orbits per side and simulated
annealing over whole voltage vectors. This version uses single-orbit bi-Cayley graphs
over semidirect products Z_m x| Z_k2 instead. With A_g ~ B_{g s} for s in a
connection set S of size d, the graph is d-regular and bipartite. Left multiplication
is an automorphism that is transitive on each side, so only two BFS roots are needed.
The search is a tabu search over the connection set, with BFS evaluated by numpy
bitmask-style frontier sweeps. Group orders are aimed just above half the record.

Safe fallbacks (K_{d,d}, projective-plane incidence, Araujo-Pardo-Lopez) are always
kept, and every candidate is checked with lib.is_valid before it is accepted.
"""
import math
import random
import time

import numpy as np

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _right_perm(m, k2, r, s):
    """Python-int permutation g -> g * s in Z_m x| Z_k2 (element (a, b) coded as a*k2 + b)."""
    G = m * k2
    c, dd = divmod(s, k2)
    out = []
    for g in range(G):
        a, b = divmod(g, k2)
        out.append(((a + pow(r, b, m) * c) % m) * k2 + (b + dd) % k2)
    return out


def _make_ops(m, k2, r):
    """Numpy right-multiplication and inverse-multiplication maps, cached per element.

    ops(s) returns (rp, lp) with rp[g] = g*s and lp[h] = h*s^{-1}.
    """
    G = m * k2
    pw = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
    xs = np.arange(G, dtype=np.int64)
    A_ = xs // k2
    B_ = xs % k2
    cache = {}

    def rp_of(s):
        c, dd = divmod(s, k2)
        return ((A_ + pw[B_] * c) % m) * k2 + (B_ + dd) % k2

    def ops(s):
        got = cache.get(s)
        if got is None:
            a, b = divmod(s, k2)
            nb = (-b) % k2
            si = ((-int(pw[nb]) * a) % m) * k2 + nb
            got = (rp_of(s), rp_of(si))
            cache[s] = got
        return got

    return G, ops


def _cost(G, D, pairs):
    """Unreached (root, vertex) pairs for the single-orbit graph; zero means diameter <= D.

    Roots are the identity on side A and the identity on side B. Left multiplication is
    transitive on each side, so these two roots cover all pairs.
    """
    total = 0
    for side in (0, 1):
        seen = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        seen[side][0] = True
        frontier = np.array([0], dtype=np.int64)
        cur = side
        for _ in range(D):
            maps = [p[0] if cur == 0 else p[1] for p in pairs]
            nb = np.concatenate([mp[frontier] for mp in maps])
            mark = np.zeros(G, dtype=bool)
            mark[nb] = True
            new = mark & ~seen[1 - cur]
            if not new.any():
                break
            seen[1 - cur] |= new
            frontier = np.flatnonzero(new)
            cur = 1 - cur
        total += 2 * G - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _search(m, k2, r, d, D, rng, deadline):
    """Tabu search for a d-element connection set S in the group with cost zero. Returns S or None."""
    G, ops = _make_ops(m, k2, r)
    if G < d + 1:
        return None

    def cost_of(S):
        return _cost(G, D, [ops(s) for s in S])

    S = rng.sample(range(G), d)
    cur = cost_of(S)
    best_c = cur
    tabu = {}
    stall = 0
    it = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        it += 1
        if stall > 120:
            S = rng.sample(range(G), d)
            cur = cost_of(S)
            best_c = cur
            stall = 0
            tabu = {}
            continue
        p = rng.randrange(d)
        inS = set(S)
        pool = rng.sample(range(G), min(G, 48))
        bestx, bc = None, None
        for x in pool:
            if x in inS or tabu.get(x, -1) >= it:
                continue
            T = S[:]
            T[p] = x
            c = cost_of(T)
            if bc is None or c < bc or (c == bc and rng.random() < 0.5):
                bc, bestx = c, x
        if bestx is None:
            continue
        tabu[S[p]] = it + 4
        S[p] = bestx
        cur = bc
        if cur < best_c:
            best_c = cur
            stall = 0
        else:
            stall += 1
    return S


def _pick_group(G, rng):
    """Return (m, k2, r) with m * k2 = G, mostly non-cyclic semidirect products."""
    ks = [k for k in range(2, 13) if G % k == 0 and G // k >= 2]
    if ks and rng.random() < 0.85:
        k2 = rng.choice(ks)
        m = G // k2
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            return m, k2, rng.choice(rs)
    if G >= 2:
        return G, 1, 1
    return None


def _graph_from(m, k2, r, S):
    """Edge list of the bi-Cayley graph A_g ~ B_{g s} for s in S."""
    G = m * k2
    E = set()
    for s in S:
        rp = _right_perm(m, k2, r, s)
        for g in range(G):
            E.add((g, G + rp[g]))
    return 2 * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 3 and d >= 2:
        half_moore = max(1, moore // 2)
        floor_guess = int(0.44 * half_moore)
        budget = max(3.0, 0.08 * time_limit)
        while time.monotonic() < deadline - 0.2 and best_n < moore:
            half = best_n // 2
            window = max(4, half // 25)
            if rng.random() < 0.5:
                lo = max(half + 1, floor_guess)
            else:
                lo = half + 1
            G = lo + rng.randrange(window)
            g = _pick_group(G, rng)
            if g is None:
                continue
            m, k2, r = g
            gd = min(deadline, time.monotonic() + budget)
            S = _search(m, k2, r, d, D, rng, gd)
            if S is not None:
                n, e = _graph_from(m, k2, r, S)
                consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
