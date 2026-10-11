import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: PG(2, q) incidence graph plus two independent "arc" extensions.
#
# Let q be the largest prime power with q + 1 <= d, and s = d - q - 1 the spare
# degree on every original vertex. Choose
#   S = set of points   with at most s points of S on any line,
#   T = set of lines    with at most s lines of T through any point.
# Add a vertex a_P for each P in S, joined to the q+1 lines through P, and a
# vertex b_L for each L in T, joined to the q+1 points on L.
#
# Degrees: original line L gets q+1 + |S ∩ L| <= d, original point P gets
# q+1 + #{L in T : P in L} <= d. New vertices have degree q+1 <= d.
# Diameter 3 holds: same-side pairs are at distance <= 2 through the line PP'
# (for a_P, a_P') or the point L ∩ L' (for b_L, b_L'); a_P to b_L is always at
# distance 3 via any line L' through P meeting L at a point Q.
#
# Caveat: for d = 16 (q = 13, s = 2) each of S and T is a 2-arc, so |S|, |T| <= 14
# and this family reaches exactly 2*183 + 28 = 394, the record, not beyond it.
# Beating the record needs a different base or more slack, which this program
# does not provide. Leftover spare degree is filled with diameter-preserving twins.
#
# Safe fallbacks: K_{d,d} for D >= 2, C_{2D} for d = 2, K_2 for d = 1.
# Every candidate is checked with lib.is_valid before it is returned.
# ----------------------------------------------------------------------------


def _largest_pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _sa_select(adj, nc, s, rng, deadline):
    """Simulated annealing for a large set of items with at most s chosen items per container.

    adj[i] lists the containers of item i. nc is the number of containers.
    Adding an outside item x removes every chosen item sharing a saturated container
    with x, so the load invariant (<= s per container) is always kept.
    Returns the largest feasible item list seen.
    """
    m = len(adj)
    if m == 0:
        return []
    load = [0] * nc
    members = [set() for _ in range(nc)]
    chosen = [False] * m
    cur = 0
    best_size = 0
    best = []
    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    T = 1.0
    it = 0
    while True:
        it += 1
        if (it & 63) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = max(0.02, 1.0 * (0.03 ** ((now - t0) / span)))
        x = rng.randrange(m)
        if chosen[x]:
            continue
        R = set()
        for c in adj[x]:
            if load[c] >= s:
                R |= members[c]
        delta = 1 - len(R)
        if delta >= 0 or rng.random() < math.exp(delta / T):
            for y in R:
                chosen[y] = False
                for c in adj[y]:
                    load[c] -= 1
                    members[c].discard(y)
            chosen[x] = True
            for c in adj[x]:
                load[c] += 1
                members[c].add(x)
            cur += delta
            if cur > best_size:
                best_size = cur
                best = [i for i in range(m) if chosen[i]]
    return best


def _pg_extension(d, q, seed, deadline):
    """PG(2,q) incidence plus independent point-arc and line-arc extensions. Returns (n, edges)."""
    n0, base = lib.projective_plane_incidence(q)
    m = n0 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in base:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)

    s = d - q - 1
    S, T = [], []
    if s >= 1:
        now = time.monotonic()
        span = max(deadline - now, 0.0)
        rng_s = random.Random(seed * 31 + 1)
        rng_t = random.Random(seed * 31 + 2)
        # S: items are points, containers are lines.
        S = _sa_select(point_lines, m, s, rng_s, now + 0.45 * span)
        # T: items are lines, containers are points.
        T = _sa_select(line_points, m, s, rng_t, now + 0.90 * span)

    edges = list(base)
    n = n0
    for t, P in enumerate(S):
        a = n0 + t
        for L in point_lines[P]:
            edges.append((a, m + L))
    off = n0 + len(S)
    for t, L in enumerate(T):
        b = off + t
        for Q in line_points[L]:
            edges.append((Q, b))
    n = off + len(T)
    return n, edges


def _twins(n, edges, d, rng, deadline):
    """Add twins (same neighbourhood as an existing vertex) while the neighbours have spare degree.

    Twins preserve distances among old vertices and keep the graph bipartite,
    so the diameter is unchanged and the degree bound is maintained.
    """
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    while time.monotonic() < deadline:
        elig = [v for v in range(n)
                if adj[v] and all(len(adj[u]) < d for u in adj[v])]
        if not elig:
            break
        v = rng.choice(elig)
        t = n
        n += 1
        adj.append(list(adj[v]))
        for u in adj[t]:
            adj[u].append(t)
            edges.append((u, t))
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        q = _largest_pg_q(d)
        if q is not None:
            n1, e1 = _pg_extension(d, q, seed, start + 0.8 * (deadline - start))
            consider(n1, e1)
            rng_tw = random.Random(seed * 104729 + 17)
            n2, e2 = _twins(best_n, best_e, d, rng_tw, deadline)
            consider(n2, e2)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
