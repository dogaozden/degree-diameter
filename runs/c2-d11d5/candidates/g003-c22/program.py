import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact or near-exact baselines (kept as fallbacks and for calibration cases).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (small q only, for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: bi-Cayley ("Haar-type") graphs over ABELIAN groups.
#
# Group G = Z_a x Z_b (or cyclic Z_G). Vertices A_g and B_g for g in G, with
# A_g ~ B_{g+s} for s in S, |S| = d. Every vertex has degree exactly d, the graph
# is bipartite, and translation is an automorphism of each side. So diameter <= D
# holds iff every vertex is within distance D of A_0 and of B_0.
#
# Search: simulated annealing over the connection set S, with a fast numpy
# reachability cost (unreached vertices from the two sources). The target order
# climbs above the best valid graph found so far, with an adaptive step size.
# This is a different family from the block-structured semidirect lifts.
# ----------------------------------------------------------------------------


def _moduli(G, rng):
    """Return the moduli of a random abelian group of order G (cyclic or two factors)."""
    divs = [a for a in range(2, G) if G % a == 0 and G // a >= 2]
    if divs and rng.random() < 0.6:
        a = rng.choice(divs)
        return [a, G // a]
    return [G]


class _Group:
    """Abelian group Z_m1 x ... x Z_mk with elements coded in mixed radix."""

    def __init__(self, mods):
        self.mods = list(mods)
        G = 1
        for m in self.mods:
            G *= m
        self.G = G
        x = np.arange(G, dtype=np.int64)
        strides = []
        st = 1
        for m in reversed(self.mods):
            strides.append(st)
            st *= m
        strides.reverse()
        self.strides = strides
        self.coords = [(x // s) % m for s, m in zip(strides, self.mods)]

    def vec(self, s):
        return [(s // st) % m for st, m in zip(self.strides, self.mods)]

    def shift(self, s, sign):
        """Array of the index of x + sign*s for every element x."""
        v = self.vec(s)
        idx = np.zeros(self.G, dtype=np.int64)
        for c, (st, m) in enumerate(zip(self.strides, self.mods)):
            idx += ((self.coords[c] + sign * v[c]) % m) * st
        return idx


def _set_col(nbr, G, grp, j, s):
    """Set column j of the neighbour table for connection element s."""
    nbr[:G, j] = G + grp.shift(s, 1)     # A_x ~ B_{x+s}
    nbr[G:, j] = grp.shift(s, -1)        # B_y ~ A_{y-s}


def _cost(nbr, N, G, D):
    """Number of (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    total = 0
    for src in (0, G):
        reached = np.zeros(N, dtype=bool)
        reached[src] = True
        cnt = 1
        for _ in range(D):
            new = reached | reached[nbr].any(axis=1)
            c2 = int(np.count_nonzero(new))
            reached = new
            if c2 == cnt or c2 == N:
                cnt = c2
                break
            cnt = c2
        total += N - cnt
    return total


def _search(d, D, grp, rng, deadline, iters):
    """Anneal the connection set S. Returns the neighbour table (N x d) on success, else None."""
    G = grp.G
    N = 2 * G
    S = rng.sample(range(G), d)
    nbr = np.empty((N, d), dtype=np.int64)
    for j, s in enumerate(S):
        _set_col(nbr, G, grp, j, s)
    cost = _cost(nbr, N, G, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[j]
        S[j] = new
        _set_col(nbr, G, grp, j, new)
        c2 = _cost(nbr, N, G, D)
        temp = max(0.4, 3.0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[j] = old
            _set_col(nbr, G, grp, j, old)
    if cost == 0:
        return nbr
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: abelian bi-Cayley graphs climbing above the current best order.
    f = 0.05
    fails = 0
    while time.monotonic() < deadline:
        best_G = best_n // 2
        step = 1 + rng.randrange(max(1, int(best_G * f)))
        Gc = max(d, best_G + step)
        mods = _moduli(Gc, rng)
        grp = _Group(mods)
        if grp.G < d:
            continue
        nbr = _search(d, D, grp, rng, deadline, 2500)
        if nbr is None:
            fails += 1
            if fails % 3 == 0:
                f = max(0.002, f * 0.7)
            continue
        fails = 0
        f = min(0.1, f * 1.3)
        G = grp.G
        edges = [(u, v) for u in range(G) for v in nbr[u].tolist()]
        consider(2 * G, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
