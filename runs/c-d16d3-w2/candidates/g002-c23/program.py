"""Arc-extended projective-plane graphs (D = 3) plus a generic repair search.

Parent family: the incidence graph of PG(2, q) with independent point-side
(A) and line-side (B) extension sets, each set satisfying a per-element load
limit s = d - q - 1. For d = 16 and q = 13 (s = 2) each side is capped at a
(<=2)-set, i.e. an arc, so 14 + 14 extra vertices is the ceiling for this
family: order 2*183 + 28 = 394. That matches the record, so the family cannot
beat it.

Change: keep the arc graph as a start point, then run a different search that
treats the graph as a general bipartite graph (sides fixed by 2-colouring).
Every iteration removes a random cross edge and re-links its freed endpoints to
other deficient vertices of opposite sides. Simulated annealing minimises the
number of vertex pairs farther apart than D. When the cost reaches zero the
graph is valid, so one new vertex is added and the search continues. Every
candidate is checked with lib.is_valid before it can replace the fallback.

Fallbacks: K_{d,d} (diameter 2, valid for D >= 2), then the best validated arc
graph. The repair search only returns graphs that passed lib.is_valid.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (valid for D >= 3).
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


def _pg_data(q):
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


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy load-constrained set."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generic bipartite repair search (new in this version).
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of a bipartite graph."""
    adj = lib.adjacency(n, edges)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _attach(v, side, adj, d, rng):
    """Join vertex v to random deficient vertices on the opposite side, up to degree d."""
    n = len(side)
    cand = [x for x in range(n)
            if side[x] != side[v] and len(adj[x]) < d and x not in adj[v]]
    rng.shuffle(cand)
    for x in cand:
        if len(adj[v]) >= d:
            break
        adj[v].add(x)
        adj[x].add(v)


def _repair(d, D, base, deadline, rng):
    """Annealed vertex insertion with cross-edge rewiring; returns the best validated (n, edges)."""
    n0, edges0 = base
    best_n, best_e = n0, list(edges0)
    side = _two_color(n0, edges0)
    adj = [set() for _ in range(n0)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    n = n0
    cost = _bad(n, adj, D)
    T = 1.0
    while time.monotonic() < deadline:
        if cost == 0:
            E = [(u, v) for u in range(n) if side[u] == 0 for v in adj[u]]
            if n > best_n and lib.is_valid(n, E, d, D):
                best_n, best_e = n, E
            # Grow: add one vertex on the alternating side and attach it.
            n += 1
            side.append(0 if (n - n0) % 2 == 1 else 1)
            adj.append(set())
            _attach(n - 1, side, adj, d, rng)
            cost = _bad(n, adj, D)
            T = 1.0
            continue

        T = max(0.05, T * 0.9995)
        u = rng.randrange(n)
        if not adj[u]:
            continue
        v = rng.choice(sorted(adj[u]))
        adj[u].discard(v)
        adj[v].discard(u)
        D0 = [x for x in range(n) if side[x] == 0 and len(adj[x]) < d]
        D1 = [x for x in range(n) if side[x] == 1 and len(adj[x]) < d]
        pair = None
        if D0 and D1:
            for _ in range(30):
                a = rng.choice(D0)
                b = rng.choice(D1)
                if b not in adj[a] and not (a == u and b == v):
                    pair = (a, b)
                    break
        if pair is None:
            adj[u].add(v)
            adj[v].add(u)
            continue
        a, b = pair
        adj[a].add(b)
        adj[b].add(a)
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            adj[a].discard(b)
            adj[b].discard(a)
            adj[u].add(v)
            adj[v].add(u)

    return best_n, best_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best
    best_n = best[0]

    def consider(c):
        nonlocal best, best_n
        if c is not None and c[0] > best_n and lib.is_valid(c[0], c[1], d, D):
            best = c
            best_n = c[0]

    # Arc-extended projective-plane candidates (valid for D >= 3).
    arc_deadline = start + 0.3 * time_limit
    cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
    for c in sorted(cands, key=lambda t: -t[0]):
        consider(c)

    # Generic repair search from the best validated graph, skipped at the Moore bound.
    if best_n < lib.moore_bound(d, D):
        repair_deadline = start + 0.8 * time_limit
        consider(_repair(d, D, best, repair_deadline, rng))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
