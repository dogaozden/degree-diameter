import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base family: PG(2, q) incidence, optionally extended by an arc of conic-type
# points. Each arc point P gets a new A-vertex joined to the lines through P, and
# each arc line gets a new B-vertex joined to the points on it. Valid for D = 3
# when every line carries at most s = d - q - 1 arc points (s >= 2 for the conic).
# ----------------------------------------------------------------------------

def _pg_base(q, conic):
    """Return (n, edges) for PG(2, q) incidence, plus an arc extension if conic is True."""
    n2, edges = lib.projective_plane_incidence(q)
    edges = [tuple(e) for e in edges]
    if not conic:
        return n2, edges
    m = n2 // 2
    pts = lib.projective_points(q)
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, L in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[L]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def _side_of(n, edges):
    """Two-colouring of a bipartite graph (isolated vertices get colour 0)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return side


# ----------------------------------------------------------------------------
# New helper: pair-cover annealing.
#
# For a bipartite graph, diameter <= 3 is equivalent (given no isolated vertex)
# to: every two vertices on the same side share a neighbour. Indeed, for a on
# side 0 and b on side 1 non-adjacent, pick any neighbour x of a; x and b lie on
# the same side, so they share a neighbour y, giving the path a-x-y-b.
#
# So the cost is simply the number of same-side pairs with disjoint neighbourhoods.
# We keep neighbourhoods as bitmasks, so a pair test is one AND. The search is a
# simulated annealing over degree-respecting moves (add an edge, double-edge swap,
# or move one endpoint of an edge), run on a graph with one extra isolated vertex.
# ----------------------------------------------------------------------------

def _pair_anneal(n, side, edges, d, deadline, rng):
    """Anneal toward zero same-side uncovered pairs. Returns an edge list or None."""
    adj = [set() for _ in range(n)]
    mask = [0] * n
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
        mask[u] |= 1 << v
        mask[v] |= 1 << u
    part = ([v for v in range(n) if side[v] == 0],
            [v for v in range(n) if side[v] == 1])
    everyone = list(range(n))

    def local(C):
        """Uncovered same-side pairs that involve at least one vertex of C (each counted once)."""
        Cs = set(C)
        cnt = 0
        for v in Cs:
            mv = mask[v]
            for w in part[side[v]]:
                if w == v or (w in Cs and w < v):
                    continue
                if (mv & mask[w]) == 0:
                    cnt += 1
        return cnt

    def setedge(u, v, on):
        if on:
            adj[u].add(v)
            adj[v].add(u)
            mask[u] |= 1 << v
            mask[v] |= 1 << u
        else:
            adj[u].discard(v)
            adj[v].discard(u)
            mask[u] &= ~(1 << v)
            mask[v] &= ~(1 << u)

    cost = local(everyone)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 0.6, 0.04
    T = T0
    it = 0
    while cost > 0:
        it += 1
        if (it & 31) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        r = rng.random()
        if r < 0.35:
            # add an edge between a side-0 and a side-1 vertex with spare degree
            a = rng.choice(part[0])
            b = rng.choice(part[1])
            if b in adj[a] or len(adj[a]) >= d or len(adj[b]) >= d:
                continue
            rem, add = [], [(a, b)]
        elif r < 0.7:
            # double-edge swap: keeps all degrees
            a = rng.choice(everyone)
            if not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            c = rng.choice(part[side[a]])
            if c == a or not adj[c]:
                continue
            e = rng.choice(tuple(adj[c]))
            if e in adj[a] or b in adj[c] or b == e:
                continue
            rem, add = [(a, b), (c, e)], [(a, e), (c, b)]
        else:
            # relocate: keep endpoint x, move the other end to a spare vertex z
            x = rng.choice(everyone)
            if not adj[x]:
                continue
            y = rng.choice(tuple(adj[x]))
            z = rng.choice(part[side[y]])
            if z == y or z in adj[x] or len(adj[z]) >= d:
                continue
            rem, add = [(x, y)], [(x, z)]

        C = set()
        for u, v in rem + add:
            C.add(u)
            C.add(v)
        before = local(C)
        for u, v in rem:
            setedge(u, v, False)
        for u, v in add:
            setedge(u, v, True)
        delta = local(C) - before
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost += delta
        else:
            for u, v in add:
                setedge(u, v, False)
            for u, v in rem:
                setedge(u, v, True)

    if cost != 0:
        return None
    out = []
    for u in part[0]:
        for v in adj[u]:
            out.append((u, v))
    return out


def _grow(n, edges, d, deadline, rng):
    """Repeatedly add one isolated vertex (alternating sides) and anneal it into the graph."""
    cur_n, cur_e = n, list(edges)
    cur_side = _side_of(n, cur_e)
    best = (cur_n, cur_e)
    c = 0
    fails = 0
    while fails < 2:
        now = time.monotonic()
        if now >= deadline:
            break
        share = 0.5 * (deadline - now)
        s2 = cur_side + [c]
        res = _pair_anneal(cur_n + 1, s2, cur_e, d, now + share, rng)
        if res is not None:
            cur_n += 1
            cur_side = s2
            cur_e = res
            best = (cur_n, cur_e)
            fails = 0
        else:
            fails += 1
        c ^= 1
    return best


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

    if D >= 3:
        # Projective-plane and arc-extended bases (diameter 3).
        for q in range(d - 1, 1, -1):
            if not lib.is_prime_power(q):
                continue
            s = d - q - 1
            if s < 0:
                continue
            for conic in ((False, True) if s >= 2 else (False,)):
                n, e = _pg_base(q, conic)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)

        # New helper: grow the best base by annealing extra vertices into it.
        # Only worth doing for real-sized bases; tiny cases return immediately.
        if D == 3 and best[0] >= 100 and time.monotonic() < deadline:
            n, e = _grow(best[0], best[1], d, deadline, rng)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
