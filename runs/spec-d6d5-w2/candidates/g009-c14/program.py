import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: projective plane (D = 3), Araujo-Pardo-Lopez (D = 3),
# generalized quadrangle W(q) incidence (D >= 4), and K_{d,d} as the safe fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley (single-orbit) lifts over finite groups of order G.
#
# Vertices: A_g = g and B_h = G + h, for g, h in the group.
# Darts s_1..s_d (distinct group elements) give edges A_g -- B_{g*s_i}.
# The group acts on A and on B by left multiplication, so the diameter is
# certified by two BFS runs: one from A_e and one from B_e.
# Groups: semidirect products Z_m x| Z_k (k | G, k <= 12), including cyclic
# (k = 1) and direct products (r = 1). Every such lift is d-regular, bipartite,
# and simple by construction.
# ----------------------------------------------------------------------------

def _group(G, rng):
    """Random semidirect product Z_m x| Z_k of order G, returned as (order, mul, inv)."""
    divs = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    k = rng.choice(divs)
    m = G // k
    r = 1
    if k > 1 and rng.random() < 0.9:
        cands = []
        for _ in range(150):
            x = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(x, m) == 1 and pow(x, k, m) == 1 % m:
                cands.append(x)
        if cands:
            r = rng.choice(cands)
    return lib.semidirect_group(m, k, r)


class _Lift:
    """Caches right-multiplication tables for one group."""

    def __init__(self, G, mul, inv):
        self.G = G
        self.mul = mul
        self.inv = inv
        self.R = {}
        self.Q = {}

    def rtab(self, s):
        """Table g -> g*s."""
        t = self.R.get(s)
        if t is None:
            t = [self.mul(g, s) for g in range(self.G)]
            self.R[s] = t
        return t

    def qtab(self, s):
        """Table h -> h*s^{-1}, giving the A-neighbour of B_h along dart s."""
        t = self.Q.get(s)
        if t is None:
            si = self.inv(s)
            t = [self.mul(h, si) for h in range(self.G)]
            self.Q[s] = t
        return t


def _reach(R, Q, G, side, D):
    """Number of vertices within distance D of the identity on the given side (both sides counted)."""
    seen = (bytearray(G), bytearray(G))
    seen[side][0] = 1
    count = 1
    frontier = [0]
    cur = side
    for _ in range(D):
        tabs = R if cur == 0 else Q
        mark = seen[1 - cur]
        nxt = []
        for u in frontier:
            for t in tabs:
                v = t[u]
                if not mark[v]:
                    mark[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
        cur = 1 - cur
    return count


def _cost(L, darts, D):
    """Number of vertices not reached within D from A_e and from B_e. Zero means valid."""
    G = L.G
    R = [L.rtab(s) for s in darts]
    Q = [L.qtab(s) for s in darts]
    rA = _reach(R, Q, G, 0, D)
    rB = _reach(R, Q, G, 1, D)
    return 4 * G - rA - rB


def _anneal(L, d, D, rng, deadline, iters):
    """Simulated annealing over the d distinct darts. Returns (darts or None, cost)."""
    G = L.G
    darts = rng.sample(range(G), d)
    cur = _cost(L, darts, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        s = rng.randrange(G)
        if s in darts:
            continue
        old = darts[i]
        darts[i] = s
        c2 = _cost(L, darts, D)
        T = max(0.05, 1.5 * (1 - it / iters))
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            darts[i] = old
    return (list(darts) if cur == 0 else None), cur


def _edges(L, darts):
    """Full edge list of the lift: vertices 0..2G-1, A_g = g, B_h = G + h."""
    G = L.G
    E = []
    for s in darts:
        t = L.rtab(s)
        for g in range(G):
            E.append((g, G + t[g]))
    return 2 * G, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
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
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing to gain.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Main search: single-orbit bi-Cayley lifts over semidirect products.
    # Each success raises the order floor, so the search climbs as it finds graphs.
    while time.monotonic() < deadline:
        lo = max(d, best_n // 2 + 1)
        span = max(6, lo // 10)
        G = rng.randint(lo, lo + span)
        try:
            order, mul, inv = _group(G, rng)
        except ValueError:
            continue
        L = _Lift(order, mul, inv)
        darts, _ = _anneal(L, d, D, rng, deadline, 700)
        if darts is not None:
            n, e = _edges(L, darts)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
