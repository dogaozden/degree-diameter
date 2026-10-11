"""Diameter-3 bipartite search for the d=16, D=3 target.

Idea: start from PG(2,q) incidence graphs (q+1 <= d), optionally with a conic/hyperoval
arc of extra vertices, then augment greedily. A new vertex on side s with neighbour set N
(opposite side, spare capacity, |N| <= d) keeps diameter <= 3 exactly when every vertex on
side s already has a neighbour in N (a dominating condition, checked by the greedy hitting
set). Every candidate is re-validated with lib.is_valid; K_{d,d} is the safe fallback.
"""

import random
import time

import lib


class _Graph:
    def __init__(self, n, edges, side):
        self.side = list(side)
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)

    def add(self, s, nbrs):
        x = len(self.side)
        nbrs = list(nbrs)
        self.side.append(s)
        self.adj.append(set(nbrs))
        for u in nbrs:
            self.adj[u].add(x)
        return x

    def edges(self):
        return [(u, v) for u in range(len(self.adj)) for v in self.adj[u] if u < v]


def _pg_base(q):
    """PG(2,q) incidence: points side 0 (ids 0..m-1), lines side 1 (ids m..2m-1)."""
    n, edges = lib.projective_plane_incidence(q)
    m = n // 2
    return _Graph(n, edges, [0] * m + [1] * m), m


def _arc_start(q):
    """PG(2,q) plus the parent's conic/hyperoval arc: an A-vertex per arc point (pencil)
    and a B-vertex per arc line (its points). Neighbourhoods are taken from the pure
    incidence graph before any addition, so B-vertices only touch old points."""
    G, m = _pg_base(q)
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    old_pencil = {P: sorted(G.adj[P]) for P in S}
    old_points = {P: sorted(G.adj[m + P]) for P in S}
    for P in S:
        G.add(0, old_pencil[P])
    for P in S:
        G.add(1, old_points[P])
    return G


def _hit(G, sigma, d, rng):
    """Greedy hitting set N on the opposite side: every vertex on side sigma gets a neighbour in N.
    Only opposite-side vertices with spare capacity are used. Returns N or None."""
    side, adj = G.side, G.adj
    n = len(side)
    targets = [w for w in range(n) if side[w] == sigma]
    cnt = {}
    for u in range(n):
        if side[u] != sigma and len(adj[u]) < d:
            cnt[u] = len(adj[u])  # all neighbours of an opposite-side vertex are on side sigma
    hit = set()
    chosen = []
    unhit = len(targets)
    while unhit:
        if len(chosen) >= d:
            return None
        cand = [(c, rng.random(), u) for u, c in cnt.items() if c > 0]
        if not cand:
            return None
        _, _, u = max(cand)
        chosen.append(u)
        del cnt[u]
        for w in adj[u]:
            if w not in hit:
                hit.add(w)
                unhit -= 1
                for x in adj[w]:
                    if x in cnt:
                        cnt[x] -= 1
    return chosen


def _augment(G, d, deadline, rng):
    """Repeatedly add a vertex on a random side whenever a dominating neighbourhood exists."""
    while time.monotonic() < deadline:
        sides = [0, 1]
        rng.shuffle(sides)
        found = None
        for sg in sides:
            for _ in range(8):
                r = _hit(G, sg, d, rng)
                if r is not None:
                    found = (sg, r)
                    break
            if found is not None:
                break
        if found is None:
            break
        G.add(found[0], found[1])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.7 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D < 3:
        return best

    qs = [q for q in range(2, d) if lib.is_prime_power(q)]
    qs.sort(reverse=True)
    qs = qs[:8]

    for idx, q in enumerate(qs):
        remain = deadline - time.monotonic()
        if remain <= 0:
            break
        if idx == 0:
            slice_t = 0.5 * remain
        else:
            slice_t = remain / (len(qs) - idx)
        for variant in (0, 1):
            try:
                G = _pg_base(q)[0] if variant == 0 else _arc_start(q)
            except Exception:
                continue
            sub = time.monotonic() + slice_t / 2.0
            rng = random.Random(seed * 1000003 + q * 7919 + variant)
            _augment(G, d, min(sub, deadline), rng)
            n = len(G.side)
            if n <= best_n:
                continue
            edges = G.edges()
            if lib.is_valid(n, edges, d, D):
                best, best_n = (n, edges), n

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
