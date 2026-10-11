import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: "same-side common neighbour" bipartite graphs.
#
# A bipartite graph in which any two vertices on the same side have a common
# neighbour has diameter <= 3: cross pairs v (side 0) and w (side 1) are joined
# by v-u-z-w, where u is any neighbour of v and z is a common neighbour of u and w.
# So we build the graph by adding vertices one at a time. A new vertex x on side t
# is valid iff its neighbourhood N(x) (on the other side, with spare degree) covers
# every existing vertex of side t, i.e. the union of the neighbourhoods of N(x)
# contains all side-t vertices. Adding vertices never breaks old pairs.
#
# Seeds:
#   * PG(2, q) incidence graph, q the largest prime power with q+1 <= d;
#   * the same graph plus a conic (plus nucleus for even q) as extra A-vertices
#     (pencils of lines through conic points) and extra B-vertices (points on
#     conic lines). This reproduces the 394-vertex record for d = 16.
# Growth is randomised greedy set cover, with random restarts from both seeds.
# Every candidate is checked with lib.is_valid before it can replace the best.
# The fallback K_{d,d} (diameter 2) is always valid for D >= 2.
# ----------------------------------------------------------------------------


def _valid_edges(adj):
    """Edge list of an adjacency-set structure, each edge once."""
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _add_vertex(adj, side, t, nbrs, d):
    """Append a new vertex on side t joined to nbrs; refuse if degrees or sides are wrong."""
    if not nbrs or len(nbrs) > d:
        return False
    for u in nbrs:
        if side[u] == t or len(adj[u]) >= d:
            return False
    x = len(adj)
    adj.append(set(nbrs))
    side.append(t)
    for u in nbrs:
        adj[u].add(x)
    return True


def _cover(adj, side, t, d, rng):
    """Randomised greedy set cover: pick <= d other-side vertices with spare degree
    whose neighbourhoods together contain every side-t vertex. Returns list or None."""
    n = len(adj)
    uncovered = {v for v in range(n) if side[v] == t}
    cands = [u for u in range(n) if side[u] != t and len(adj[u]) < d]
    chosen = []
    while uncovered:
        if len(chosen) >= d:
            return None
        best, best_key = -1, None
        for u in cands:
            g = len(adj[u] & uncovered)
            if g == 0:
                continue
            key = (g, rng.random())
            if best_key is None or key > best_key:
                best, best_key = u, key
        if best < 0:
            return None
        chosen.append(best)
        cands.remove(best)
        uncovered -= adj[best]
    return chosen


def _grow(adj, side, d, rng, deadline):
    """Keep adding covered vertices on either side until neither side can grow."""
    while time.monotonic() < deadline:
        grew = False
        order = [0, 1]
        rng.shuffle(order)
        for t in order:
            if time.monotonic() >= deadline:
                break
            nb = _cover(adj, side, t, d, rng)
            if nb is not None and _add_vertex(adj, side, t, nb, d):
                grew = True
        if not grew:
            break


def _pg_base(q):
    """PG(2,q) incidence: points 0..m-1, lines m..2m-1. Returns (m, adj, side, index)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    adj = [set() for _ in range(n2)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    side = [0] * m + [1] * m
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    return m, adj, side, index


def _conic_ids(q, index):
    """Conic (plus nucleus for even q) as point indices; the same indices name dual lines."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _seed_conic(base_adj, base_side, m, S, d):
    """Add pencil A-vertices at conic points and dual-conic B-vertices. None if it fails."""
    pencils = [sorted(base_adj[P]) for P in S]        # lines through P (side 1)
    dual_pts = [sorted(base_adj[m + P]) for P in S]   # points on line P (side 0)
    adj = [set(a) for a in base_adj]
    side = list(base_side)
    for nb in pencils:
        if not _add_vertex(adj, side, 0, nb, d):
            return None
    for nb in dual_pts:
        if not _add_vertex(adj, side, 1, nb, d):
            return None
    return adj, side


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(adj):
        nonlocal best, best_n
        n = len(adj)
        if n <= best_n:
            return
        e = _valid_edges(adj)
        if lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        qs = [q for q in range(2, min(d, 32)) if lib.is_prime_power(q) and q + 1 <= d]
        if qs:
            q = max(qs)
            m, base_adj, base_side, index = _pg_base(q)
            conic = _conic_ids(q, index)
        else:
            m, q, conic = None, None, None
            base_adj = [{1}, {0}]
            base_side = [0, 1]

        attempt = 0
        while time.monotonic() < deadline:
            attempt += 1
            seeded = None
            if conic is not None and attempt % 2 == 1:
                seeded = _seed_conic(base_adj, base_side, m, conic, d)
            if seeded is not None:
                adj, side = seeded
            else:
                adj = [set(a) for a in base_adj]
                side = list(base_side)
            _grow(adj, side, d, rng, deadline)
            consider(adj)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
