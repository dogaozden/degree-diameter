import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe algebraic fallbacks.
# ----------------------------------------------------------------------------

def _fallback(d):
    """K_{d,d}: bipartite, degree d, diameter 2. Valid for every D >= 2."""
    return lib.haar_graph(d, range(d))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: single-orbit bi-Cayley (Haar-type) graphs over groups.
#
# Vertices: left a_g and right b_h, for g, h in a group G of order N0.
# Edge set: a_g ~ b_{g*s} for s in S, where |S| = d and S has distinct elements.
# Left multiplication is an automorphism, so the diameter is exactly the
# maximum of the distances from a_e and from b_e to every vertex.
# This gives an exact diameter test using only two BFS runs, so the search can
# afford many more evaluations than a general repair search.
# ----------------------------------------------------------------------------

class _Group:
    def __init__(self, order, mul, inv):
        self.G = order
        self.mul = mul
        self.inv = inv
        self.cache = {}

    def cols(self, s):
        """Right-neighbour column for left vertices, and left-neighbour column for right vertices."""
        c = self.cache.get(s)
        if c is None:
            G, mul = self.G, self.mul
            R = np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)
            si = self.inv(s)
            L = np.fromiter((mul(h, si) for h in range(G)), dtype=np.int64, count=G)
            c = (R, L)
            self.cache[s] = c
        return c


def _nb_matrix(grp, S):
    G = grp.G
    nb = np.empty((2 * G, len(S)), dtype=np.int64)
    for j, s in enumerate(S):
        R, L = grp.cols(s)
        nb[:G, j] = G + R
        nb[G:, j] = L
    return nb


def _missing(nb, G, D):
    """Number of (source, vertex) pairs unreached within D steps, for the two sources a_e and b_e."""
    N = 2 * G
    total = 0
    for src in (0, G):
        vis = np.zeros(N, dtype=bool)
        vis[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            cand = nb[front].ravel()
            cand = cand[~vis[cand]]
            if cand.size == 0:
                break
            cand = np.unique(cand)
            vis[cand] = True
            front = cand
        total += N - int(vis.sum())
    return total


def _anneal(grp, d, D, rng, deadline, iters):
    """Simulated annealing over the connection set S (size d). Returns S with diameter <= D, or None."""
    G = grp.G
    if d > G:
        return None
    S = rng.sample(range(G), d)
    nb = _nb_matrix(grp, S)
    cur = _missing(nb, G, D)
    t = 0
    while cur > 0 and t < iters:
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        t += 1
        j = rng.randrange(d)
        e = rng.randrange(G)
        if e in S:
            continue
        old = S[j]
        S[j] = e
        nb2 = nb.copy()
        R, L = grp.cols(e)
        nb2[:G, j] = G + R
        nb2[G:, j] = L
        c2 = _missing(nb2, G, D)
        temp = max(0.05, 1.5 * (1.0 - t / iters))
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            nb = nb2
            cur = c2
        else:
            S[j] = old
    if cur == 0:
        return S
    return None


def _edges(grp, S):
    G = grp.G
    E = []
    for s in S:
        R, _ = grp.cols(s)
        for g, h in enumerate(R.tolist()):
            E.append((g, G + h))
    return 2 * G, E


def _group_options(G, rng, limit=3):
    """Semidirect products Z_m x| Z_k2 with m * k2 = G (cyclic group included as k2 = 1)."""
    opts = []
    for k2 in range(1, min(G, 40) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        rng.shuffle(cands)
        opts += [(m, k2, r) for r in cands[:limit]]
    rng.shuffle(opts)
    return opts


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d)
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
            if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
                return best

    try:
        if d >= 3 and D >= 2:
            while time.monotonic() < deadline - 0.5:
                remaining = deadline - time.monotonic()
                target = best_n // 2 + 1
                G = target + rng.randrange(0, max(2, target // 30) + 1)
                opts = _group_options(G, rng)
                if not opts:
                    continue
                slice_end = min(deadline, time.monotonic() + max(1.5, 0.2 * remaining))
                found = None
                for (m, k2, r) in opts[:3]:
                    if time.monotonic() > slice_end:
                        break
                    order, mul, inv = lib.semidirect_group(m, k2, r)
                    grp = _Group(order, mul, inv)
                    S = _anneal(grp, d, D, rng, slice_end, 6000)
                    if S is not None:
                        found = (grp, S)
                        break
                if found is not None:
                    n, E = _edges(*found)
                    consider(n, E)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d)
    return best
