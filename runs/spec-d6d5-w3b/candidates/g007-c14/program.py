import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base families: projective plane, Araujo-Pardo-Lopez (D = 3), generalized
# quadrangle W(q) (D = 4). These are also the bases for the lift search.
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
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are 0..P-1, lines are P..2P-1. Every vertex has degree q + 1. Diameter 4.
    """
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to q <= 9."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW construction for D >= 5: random Z_m voltage lifts of a d-regular bipartite
# base (the generalized quadrangle incidence graph for q = d - 1 <= 9, else the
# projective plane incidence graph). Lift vertex (x, g) is x*m + g. Lifts over
# abelian groups are Z_m-symmetric, so the search is simulated annealing over
# edge voltages, scored by the number of ordered pairs farther than D apart.
# A spanning tree of the base gets voltage 0 (gauge fixing: no loss of generality).
# Distances are computed with bit-parallel numpy reachability bitsets.
# ----------------------------------------------------------------------------

class _Lift:
    """Z_m voltage lift of a d-regular bipartite base graph with fast distance checks."""

    def __init__(self, nb, edges, d, m, D):
        self.m, self.d, self.D = m, d, D
        self.N = nb * m
        M = len(edges)
        self.EU = np.array([u for u, _ in edges], dtype=np.int64)
        self.EV = np.array([v for _, v in edges], dtype=np.int64)
        cnt = [0] * nb
        su, sv = [0] * M, [0] * M
        for i, (u, v) in enumerate(edges):
            su[i] = cnt[u]
            cnt[u] += 1
            sv[i] = cnt[v]
            cnt[v] += 1
        self.SU = np.array(su, dtype=np.int64)
        self.SV = np.array(sv, dtype=np.int64)
        self.G = np.arange(m, dtype=np.int64)
        self.base_nbr = np.repeat(np.arange(self.N, dtype=np.int64)[:, None], d, axis=1)
        W = (self.N + 63) // 64
        idx = np.arange(self.N, dtype=np.int64)
        init = np.zeros((self.N, W), dtype=np.uint64)
        init[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
        self.init = init

    def nbr(self, volt):
        """Neighbour table (N x d) of the lift for the given voltages (numpy int64 array)."""
        m = self.m
        Ua = self.EU[:, None] * m + self.G[None, :]
        Vb = self.EV[:, None] * m + (self.G[None, :] + volt[:, None]) % m
        nb = self.base_nbr.copy()
        nb[Ua, self.SU[:, None]] = Vb
        nb[Vb, self.SV[:, None]] = Ua
        return nb

    def bad(self, volt):
        """(ordered pairs at distance > D, neighbour table)."""
        nb = self.nbr(volt)
        reach = self.init
        for _ in range(self.D):
            new = reach.copy()
            for k in range(self.d):
                new |= reach[nb[:, k]]
            reach = new
        total = int(np.unpackbits(reach.view(np.uint8)).sum())
        return self.N * self.N - total, nb

    def edges(self, nb):
        """Edge list of the lift from its neighbour table (each edge once)."""
        src = np.repeat(np.arange(self.N, dtype=np.int64), self.d)
        dst = nb.reshape(-1)
        keep = src < dst
        return [(int(a), int(b)) for a, b in zip(src[keep], dst[keep])]


def _tree_edges(nb, edges):
    """Indices of a BFS spanning tree of the base graph."""
    adj = [[] for _ in range(nb)]
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    seen = [False] * nb
    seen[0] = True
    queue = [0]
    tree = set()
    h = 0
    while h < len(queue):
        x = queue[h]
        h += 1
        for y, i in adj[x]:
            if not seen[y]:
                seen[y] = True
                tree.add(i)
                queue.append(y)
    return tree


def _anneal(lift, volt, free, rng, deadline):
    """Annealing over non-tree voltages. Returns (best_cost, best_neighbour_table)."""
    cur, nb = lift.bad(volt)
    best, best_nb = cur, nb
    m = lift.m
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = max(0.15, 3.0 * (1.0 - frac))
        e = free[rng.randrange(len(free))]
        old = int(volt[e])
        new = rng.randrange(m)
        if new == old:
            continue
        volt[e] = new
        c, nb2 = lift.bad(volt)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
            if c < best:
                best, best_nb = c, nb2
        else:
            volt[e] = old
    return best, best_nb


def _try_lift(nb, bedges, d, D, m, deadline, rng):
    """Search for a valid Z_m lift of the base; return (n, edges) or None."""
    lift = _Lift(nb, bedges, d, m, D)
    tree = _tree_edges(nb, bedges)
    free = [i for i in range(len(bedges)) if i not in tree]
    if not free:
        return None
    volt = np.array([rng.randrange(m) for _ in bedges], dtype=np.int64)
    for i in tree:
        volt[i] = 0
    best, best_nb = _anneal(lift, volt, free, rng, deadline)
    if best == 0:
        return lift.N, lift.edges(best_nb)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.82 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = list(lib.haar_graph(d, range(d)))

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
        ar = _araujo(d)
        if ar is not None:
            consider(*ar)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(*gq)

    # New bold family for D >= 5: voltage lifts of a d-regular bipartite base.
    if D >= 5 and d >= 3:
        q = d - 1
        base = None
        if lib.is_prime_power(q):
            if q <= 9:
                base = _gq_w(q)
            else:
                base = lib.projective_plane_incidence(q)
        if base is not None:
            nb, bedges = base
            deg = [0] * nb
            for u, v in bedges:
                deg[u] += 1
                deg[v] += 1
            if all(x == d for x in deg):
                tot = end - start
                # m = 2 gives a safe ~2x lift; m = 3 is the main bet (beats 684 if valid).
                stages = [
                    (2, start + 0.30 * tot),
                    (3, start + 0.70 * tot),
                    (4, end),
                ]
                for m, dl in stages:
                    if time.monotonic() >= dl:
                        continue
                    res = _try_lift(nb, bedges, d, D, m, dl, rng)
                    if res is not None:
                        consider(*res)

    n, e = best
    if not lib.is_valid(n, e, d, D):
        n, e = lib.haar_graph(d, range(d))
    return n, e
