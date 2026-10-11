import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists (one colour per component)."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# From PG(2, q), spare capacity s = d - q - 1. Choose a point set S with every
# line holding <= s points of S and every point on <= s lines of S, then add an
# A-vertex per point of S and a B-vertex per line of S.
# ----------------------------------------------------------------------------

def _pg_data(q):
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large feasible S, starting from feasible S0."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in point_lines[P] if cl[L] >= s}
        satQ = {Q for Q in line_points[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in point_lines[R])
                or any(Q in satQ for Q in line_points[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng, threshold):
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        kmax = s * m // (q + 1)
        if 2 * m + 2 * kmax <= threshold:
            continue
        qs.append((q, s))

    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        q_deadline = now + share
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, now + 0.3 * share)]
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S0 = max(cands, key=len, default=[])
        if not _loads_ok(S0, s, m, point_lines, line_points):
            S0 = []
        S = _local_arc(m, s, point_lines, line_points, S0, rng, q_deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# NEW FAMILY: growth by degree-preserving rewiring annealing.
#
# Starting from a valid graph, add one A-vertex and one B-vertex (opposite
# sides), then anneal over moves that keep every degree <= d and every edge
# bipartite: move an edge (x, y) to (x, z) with z on y's side. The cost is the
# number of vertex pairs at distance > D. A cost of zero gives a valid graph,
# which is then recorded. On failure the previous valid graph is kept.
# ----------------------------------------------------------------------------

def _anneal_repair(n, adj, side, d, D, deadline, rng):
    """Anneal in place. Returns True iff a valid (cost 0) graph was reached before the deadline."""
    lists = ([v for v in range(n) if side[v] == 0], [v for v in range(n) if side[v] == 1])

    def fill():
        # Pure additions never increase distances, so they are always safe.
        order = [v for v in range(n) if len(adj[v]) < d]
        rng.shuffle(order)
        for x in order:
            if len(adj[x]) >= d:
                continue
            cands = [z for z in lists[1 - side[x]] if len(adj[z]) < d and z not in adj[x]]
            rng.shuffle(cands)
            for z in cands:
                if len(adj[x]) >= d:
                    break
                if len(adj[z]) < d:
                    adj[x].add(z)
                    adj[z].add(x)

    def cost():
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

    fill()
    cur = cost()
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    it = 0
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        it += 1
        if it % 50 == 0:
            fill()
            cur = cost()
            continue
        x = rng.randrange(n)
        if not adj[x]:
            continue
        y = rng.choice(tuple(adj[x]))
        cands = [z for z in lists[side[y]] if z != y and len(adj[z]) < d and z not in adj[x]]
        if not cands:
            continue
        z = rng.choice(cands)
        adj[x].discard(y)
        adj[y].discard(x)
        adj[x].add(z)
        adj[z].add(x)
        c2 = cost()
        frac = min(1.0, (now - start) / span)
        T = 2.0 * (0.05 / 2.0) ** frac
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            adj[x].discard(z)
            adj[z].discard(x)
            adj[x].add(y)
            adj[y].add(x)
    return True


def _grow_repair(n, edges, d, D, deadline, rng, consider):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    side = _bipartition(n, [list(s) for s in adj])
    cur_n, cur_adj, cur_side = n, adj, side
    fails = 0
    while fails < 4:
        now = time.monotonic()
        if now >= deadline - 0.2:
            break
        step_dl = min(deadline, now + max(1.0, 0.3 * (deadline - now)))
        new_adj = [set(s) for s in cur_adj] + [set(), set()]
        new_side = list(cur_side) + [0, 1]
        if _anneal_repair(cur_n + 2, new_adj, new_side, d, D, step_dl, rng):
            cur_n += 2
            cur_adj, cur_side = new_adj, new_side
            fails = 0
            E = [(u, v) for u in range(cur_n) for v in cur_adj[u] if u < v]
            consider(cur_n, E)
        else:
            fails += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = [lib.haar_graph(d, range(d))]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        arc_deadline = start + 0.35 * budget
        for n_c, e_c in _arc_extensions(d, arc_deadline,
                                        random.Random(seed * 7919 + d), best[0][0]):
            consider(n_c, e_c)

    # Grow the best valid graph by repair annealing for the rest of the budget.
    base_n, base_e = best[0]
    _grow_repair(base_n, base_e, d, D, deadline, rng, consider)

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        return lib.haar_graph(d, range(d))
    return best[0]
