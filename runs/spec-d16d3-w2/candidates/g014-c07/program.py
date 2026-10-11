import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base construction: arc-extended projective plane incidence graph (D = 3).
# Old vertices have degree q+1; spare capacity s = d-q-1 is used by adding one
# A-vertex per arc point (joined to the lines through it) and one B-vertex per
# arc point (joined to the points on the line it indexes).
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy(m, s, pl, lp, rng, trials, deadline):
    """Randomized greedy arc-like set with all loads <= s."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _arc_base(d, rng, deadline):
    """Return (n, edges, side) for the arc-extended PG graph, or None. side[v] True = A-side."""
    q = max((x for x in range(2, d) if lib.is_prime_power(x)), default=None)
    if q is None:
        return None
    s = d - q - 1
    m, edges, pl, lp, index = _pg(q)
    S = []
    if s >= 1:
        S = _greedy(m, s, pl, lp, rng, 30, deadline)
    if s >= 2:
        F = lib.GF(q)
        cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            cs.append(index[(0, 1, 0)])
        if len(cs) > len(S) and _loads_ok(cs, s, m, pl, lp):
            S = cs
    if not _loads_ok(S, s, m, pl, lp):
        return None
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    side = [(v < m) or (2 * m <= v < 2 * m + k) for v in range(n)]
    return n, E, side


# ----------------------------------------------------------------------------
# Simulated annealing with growth (D >= 3).
# Graph is kept bipartite (edges only between A and B sides) and max degree <= d.
# Cost = number of unordered vertex pairs at distance > D.
# When cost hits 0 we add one vertex (new, high-cost) and continue annealing.
# Every stored snapshot is validated with lib.is_valid.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (bitset ball expansion)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return (n * n - sum(r.bit_count() for r in reach)) // 2


def _improve(n0, E0, side0, d, D, deadline, rng):
    best_n, best_E, best_side = n0, list(E0), list(side0)

    def load(n, E, side):
        adj = [set() for _ in range(n)]
        for u, v in E:
            adj[u].add(v)
            adj[v].add(u)
        A = [v for v in range(n) if side[v]]
        B = [v for v in range(n) if not side[v]]
        return adj, A, B

    n = n0
    side = list(side0)
    adj, A, B = load(n, E0, side)
    cur = _bad(n, adj, D)
    T = 0.6
    since = 0
    LIMIT = 2500

    while time.monotonic() < deadline:
        if cur == 0:
            if n > best_n:
                E = [(u, v) for u in range(n) for v in adj[u] if u < v]
                if lib.is_valid(n, E, d, D):
                    best_n, best_E, best_side = n, E, list(side)
            # Grow by one vertex on the side opposite to its neighbours.
            new_a = rng.random() < 0.5
            opp = B if new_a else A
            cands = [w for w in opp if len(adj[w]) < d]
            if not cands:
                break
            rng.shuffle(cands)
            x = n
            adj.append(set())
            side.append(new_a)
            (A if new_a else B).append(x)
            for w in cands[:d]:
                adj[x].add(w)
                adj[w].add(x)
            n += 1
            cur = _bad(n, adj, D)
            since = 0
            continue

        since += 1
        if since > LIMIT:
            # Restart from the best valid snapshot.
            n = best_n
            side = list(best_side)
            adj, A, B = load(n, best_E, side)
            cur = _bad(n, adj, D)
            since = 0
            T = 0.6
            continue

        T = max(0.05, T * 0.9995)
        if rng.random() < 0.3:
            # Add an edge between a random A and B pair with spare degree.
            a = rng.choice(A)
            b = rng.choice(B)
            if b in adj[a] or len(adj[a]) >= d or len(adj[b]) >= d:
                continue
            adj[a].add(b)
            adj[b].add(a)
            new = _bad(n, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                adj[a].discard(b)
                adj[b].discard(a)
        else:
            # Relocate one endpoint of a random edge (u, w) to a new neighbour y on u's side.
            u = rng.randrange(n)
            if not adj[u]:
                continue
            w = rng.choice(tuple(adj[u]))
            pool = A if side[u] else B
            y = rng.choice(pool)
            if y == u or y in adj[w] or len(adj[y]) >= d:
                continue
            adj[u].discard(w)
            adj[w].discard(u)
            adj[y].add(w)
            adj[w].add(y)
            new = _bad(n, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                adj[y].discard(w)
                adj[w].discard(y)
                adj[u].add(w)
                adj[w].add(u)

    return best_n, best_E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        base = _arc_base(d, rng, start + 0.1 * time_limit)
        if base is not None:
            n0, E0, side0 = base
            if n0 > best[0] and lib.is_valid(n0, E0, d, D):
                best = (n0, E0)
            n1, E1 = _improve(n0, E0, side0, d, D, deadline, rng)
            if n1 > best[0] and lib.is_valid(n1, E1, d, D):
                best = (n1, E1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
