import random
import time

import lib


# ----------------------------------------------------------------------------
# Exploratory construction for diameter 3: randomized covering growth.
#
# Start from the incidence graph of PG(2, q), where q is the largest prime power
# with q + 1 <= d (diameter 3, bipartite, points 0..m-1 and lines m..2m-1).
#
# Growth move: add a new vertex x on one side, joined to a set N of free
# vertices on the other side. Adding a vertex never lengthens existing
# distances, so the graph stays valid iff x reaches every vertex within 3 steps.
# Since dist(x, y) = 1 + dist(b, y) for the best b in N, this holds iff the
# radius-2 balls of the chosen b's cover all vertices. We find such N by a
# randomized greedy set cover over bitmasks.
#
# Perturbation: after many failed growth attempts, delete a random vertex if
# the result is still valid, which lets the search escape the PG-star structure.
#
# Every stored graph is validated with lib.is_valid. A safe fallback K_{d,d}
# (diameter 2) or K_2 is used when nothing better is found. This approach is
# not guaranteed to beat the 394 record for d=16, D=3.
# ----------------------------------------------------------------------------


def _fallback(d, D):
    if d < 1:
        return 1, []
    if D >= 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    return 2, [(0, 1)]


def _pg_base(d):
    """PG(2,q) incidence for the largest prime power q with q + 1 <= d."""
    for c in range(d - 1, 1, -1):
        if lib.is_prime_power(c):
            n, e = lib.projective_plane_incidence(c)
            return n, e
    return None


def _adj_from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _masks(n, adj):
    """b1[v]: bitmask of vertices within distance 1 of v; b2[v]: within distance 2."""
    b1 = []
    for v in range(n):
        m = 1 << v
        for u in adj[v]:
            m |= 1 << u
        b1.append(m)
    b2 = []
    for v in range(n):
        m = b1[v]
        for u in adj[v]:
            m |= b1[u]
        b2.append(m)
    return b1, b2


def _try_add(n, adj, b2, side, d, s, rng, full):
    """Randomized greedy cover: pick N on side 1-s with all radius-2 balls covering the graph."""
    cand = [v for v in range(n) if side[v] != s and len(adj[v]) < d]
    covered = 0
    chosen = []
    used = set()
    while covered != full:
        if len(chosen) >= d:
            return None
        scored = []
        for v in cand:
            if v in used:
                continue
            g = (b2[v] & ~covered).bit_count()
            if g > 0:
                scored.append((g, v))
        if not scored:
            return None
        if rng.random() < 0.8:
            top = max(g for g, _ in scored)
            pool = [v for g, v in scored if g == top]
        else:
            pool = [v for _, v in scored]
        v = rng.choice(pool)
        used.add(v)
        chosen.append(v)
        covered |= b2[v]
    return chosen


def _remove_vertex(n, adj, side, x):
    """Return (n-1, adj, side) with vertex x deleted and labels compacted."""
    keep = [v for v in range(n) if v != x]
    idx = {old: new for new, old in enumerate(keep)}
    new_adj = [set() for _ in keep]
    for old in keep:
        for u in adj[old]:
            if u != x:
                new_adj[idx[old]].add(idx[u])
    new_side = [side[v] for v in keep]
    return len(keep), new_adj, new_side


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    best_n, best_e = _fallback(d, D)
    if D < 3:
        return best_n, best_e

    base = _pg_base(d)
    if base is None:
        return best_n, best_e

    n0, e0 = base
    adj = _adj_from_edges(n0, e0)
    m = n0 // 2
    side = [0] * m + [1] * m
    n = n0
    if n0 > best_n and lib.is_valid(n0, e0, d, D):
        best_n, best_e = n0, e0

    b1, b2 = _masks(n, adj)
    fails = 0

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        s = rng.randrange(2)
        chosen = _try_add(n, adj, b2, side, d, s, rng, full)

        if chosen is not None:
            fails = 0
            x = n
            adj.append(set())
            side.append(s)
            n += 1
            for v in chosen:
                adj[x].add(v)
                adj[v].add(x)
            b1, b2 = _masks(n, adj)
            if n > best_n:
                e = _edges_of(adj)
                if lib.is_valid(n, e, d, D):
                    best_n, best_e = n, e
            continue

        fails += 1
        if fails >= 200 and n > 2:
            # Perturb: delete a random vertex if the graph stays valid.
            fails = 0
            for _ in range(5):
                x = rng.randrange(n)
                n2, adj2, side2 = _remove_vertex(n, adj, side, x)
                e2 = _edges_of(adj2)
                if lib.is_valid(n2, e2, d, D):
                    n, adj, side = n2, adj2, side2
                    b1, b2 = _masks(n, adj)
                    break

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return _fallback(d, D)
