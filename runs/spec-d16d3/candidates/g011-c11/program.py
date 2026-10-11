"""Bipartite diameter-3 construction: PG(2,q) incidence, blown up by vertex cloning.

Cloning a vertex (new vertex with the same neighbourhood, same side) preserves
bipartiteness and any diameter bound >= 2, and each clone raises the degree of
its neighbours by one. The main family is therefore:
  * PG(2, q) incidence with q the largest prime power <= d-1,
  * plus clones of point-vertices and line-vertices from a set S with
    spare-degree loads <= d - (q+1) (conic or greedy arcs),
  * plus greedy generic cloning with whatever spare degree remains.
For d-1 a prime power the plain incidence graph is returned (Moore-optimal).
For D = 3 with leftover time, a simulated-annealing search tries to add two
vertices (one per side) to the best blow-up graph, using degree-preserving
edge swaps and rewiring, with cost = number of pairs at distance > D.
Every result is checked with lib.is_valid before it is accepted, and the
fallback is K_{d,d}.
"""
import math
import random
import time

import lib


def _largest_pp(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _max_deg(adj):
    return max((len(a) for a in adj), default=0)


def _greedy_arc(mp, s, point_lines, line_points, rng, trials):
    """Randomized greedy S of points with every line holding <= s points of S and every point on <= s lines of S."""
    best = []
    order = list(range(mp))
    for _ in range(trials):
        rng.shuffle(order)
        cl = [0] * mp
        cp = [0] * mp
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _blow(adj0, color0, mp, S):
    """Clone each point in S (new side-0 vertex on its lines) and each line j in S (new side-1 vertex on its points)."""
    base = [set(a) for a in adj0]
    adj = [set(a) for a in adj0]
    color = list(color0)
    for P in S:
        v = len(adj)
        adj.append(set(base[P]))
        color.append(0)
        for L in base[P]:
            adj[L].add(v)
    for j in S:
        v = len(adj)
        adj.append(set(base[mp + j]))
        color.append(1)
        for Q in base[mp + j]:
            adj[Q].add(v)
    return len(adj), adj, color


def _clone_grow(n, adj, color, d, rng, deadline):
    """Repeatedly clone any vertex whose neighbours all have spare degree. Preserves diameter."""
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            nbrs = list(adj[x])
            if not nbrs or len(nbrs) > d:
                continue
            if any(len(adj[w]) >= d for w in nbrs):
                continue
            v = n
            n += 1
            adj.append(set(nbrs))
            color.append(color[x])
            for w in nbrs:
                adj[w].add(v)
            changed = True
    return n


def _bad(n, adj, D):
    """Number of unordered pairs at distance > D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _random_move(n, adj, color, sides, d, rng):
    """Propose a move as a list of ('a'|'r', u, v) operations, or None. Keeps max degree <= d."""
    r = rng.random()
    if r < 0.4:
        defi = [v for v in range(n) if len(adj[v]) < d]
        if not defi:
            return None
        u = rng.choice(defi)
        opp = [w for w in defi if color[w] != color[u] and w not in adj[u]]
        if not opp:
            return None
        return [("a", u, rng.choice(opp))]
    u = rng.randrange(n)
    if not adj[u]:
        return None
    v = rng.choice(tuple(adj[u]))
    if r < 0.75:
        # degree-preserving double edge swap
        w = rng.choice(sides[color[u]])
        if w == u or not adj[w]:
            return None
        x = rng.choice(tuple(adj[w]))
        if x == v or x in adj[u] or v in adj[w]:
            return None
        return [("r", u, v), ("r", w, x), ("a", u, x), ("a", w, v)]
    # rewire endpoint v -> x on v's side
    cand = [x for x in sides[color[v]] if x != v and len(adj[x]) < d and x not in adj[u]]
    if not cand:
        return None
    return [("r", u, v), ("a", u, rng.choice(cand))]


def _apply(adj, ops):
    for kind, u, v in ops:
        if kind == "a":
            adj[u].add(v)
            adj[v].add(u)
        else:
            adj[u].discard(v)
            adj[v].discard(u)


def _undo(adj, ops):
    for kind, u, v in reversed(ops):
        if kind == "a":
            adj[u].discard(v)
            adj[v].discard(u)
        else:
            adj[u].add(v)
            adj[v].add(u)


def _sa(n, adj, color, D, d, deadline, rng):
    """Annealing on cost = bad pairs. Returns True if a zero-cost graph was reached (adj is modified in place)."""
    sides = ([v for v in range(n) if color[v] == 0], [v for v in range(n) if color[v] == 1])
    cur = _bad(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 0.05 ** min(1.0, (now - t0) / span)  # 1.0 -> 0.05
        ops = _random_move(n, adj, color, sides, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        c2 = _bad(n, adj, D)
        if c2 <= cur - T * math.log(1.0 - rng.random()):
            cur = c2
        else:
            _undo(adj, ops)
    return cur == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2).
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        q = _largest_pp(d - 1)
        if q is not None:
            n2, E = lib.projective_plane_incidence(q)
            consider(n2, E)
            if q == d - 1 and D == 3:
                # Incidence graph of PG(2, d-1) is Moore-optimal here.
                return best_n, best_e

            mp = n2 // 2
            adj0 = [set() for _ in range(n2)]
            for u, v in E:
                adj0[u].add(v)
                adj0[v].add(u)
            color0 = [0] * mp + [1] * mp
            s = d - q - 1

            cands = [(n2, [set(a) for a in adj0], list(color0))]
            if s >= 1:
                point_lines = [[L - mp for L in adj0[P]] for P in range(mp)]
                line_points = [list(adj0[mp + j]) for j in range(mp)]
                sets = []
                if s >= 2:
                    F = lib.GF(q)
                    index = {p: i for i, p in enumerate(lib.projective_points(q))}
                    conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
                    if q % 2 == 0:
                        conic.append(index[(0, 1, 0)])
                    sets.append(conic)
                sets.append(_greedy_arc(mp, s, point_lines, line_points, rng, 30))
                for S in sets:
                    if S:
                        cands.append(_blow(adj0, color0, mp, S))

            best_blow = None
            for n_, adj_, col_ in cands:
                if _max_deg(adj_) > d:
                    continue
                n_ = _clone_grow(n_, adj_, col_, d, rng, deadline)
                consider(n_, _edges_of(adj_))
                if best_blow is None or n_ > best_blow[0]:
                    best_blow = (n_, adj_, col_)

            # Bold step for D = 3: add one vertex per side to the blow-up by annealing.
            while D == 3 and best_blow is not None and time.monotonic() < deadline:
                n_, adj_, col_ = best_blow
                adj2 = [set(a) for a in adj_] + [set(), set()]
                col2 = list(col_) + [0, 1]
                if not _sa(n_ + 2, adj2, col2, D, d, deadline, rng):
                    break
                consider(n_ + 2, _edges_of(adj2))
                best_blow = (n_ + 2, adj2, col2)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
