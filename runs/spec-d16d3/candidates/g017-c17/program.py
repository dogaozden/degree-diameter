import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Basic graph helpers.
# ----------------------------------------------------------------------------

def _ball_bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs count)."""
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


def _bipartition(n, adj):
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


def _edges_of(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


# ----------------------------------------------------------------------------
# Projective-plane arc graphs (diameter 3).
#
# PG(2, q) incidence, spare s = d - q - 1 per vertex. A point set S with at most
# s points on each line and at most s lines of S through each point gives the
# graph: one new A vertex per point of S (joined to its q+1 lines) and one new
# B vertex per line of S (joined to its q+1 points).
# ----------------------------------------------------------------------------

def _pg_structure(q):
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


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def _conic(q, index):
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _greedy(m, s, point_lines, line_points, rng, trials, deadline):
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


# ----------------------------------------------------------------------------
# Annealed vertex growth: add one A and one B vertex, then repair by
# simulated annealing over degree-preserving 2-switches and spare-degree adds,
# minimising the number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _anneal(n, adj, side, d, D, rng, deadline):
    Lv = [v for v in range(n) if side[v] == 0]
    Rv = [v for v in range(n) if side[v] == 1]
    cur = _ball_bad(n, adj, D)
    it = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        it += 1
        T = 0.8 * (0.02 ** ((it % 2000) / 2000.0))
        if rng.random() < 0.4:
            sp0 = [v for v in Lv if len(adj[v]) < d]
            sp1 = [v for v in Rv if len(adj[v]) < d]
            if not sp0 or not sp1:
                continue
            a = rng.choice(sp0)
            b = rng.choice(sp1)
            if b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            new = _ball_bad(n, adj, D)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                adj[a].discard(b)
                adj[b].discard(a)
        else:
            a = rng.choice(Lv)
            if not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            c = rng.choice(Lv)
            if c == a or not adj[c]:
                continue
            e = rng.choice(tuple(adj[c]))
            if e == b or e in adj[a] or b in adj[c]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[c].discard(e)
            adj[e].discard(c)
            adj[a].add(e)
            adj[e].add(a)
            adj[c].add(b)
            adj[b].add(c)
            new = _ball_bad(n, adj, D)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                adj[a].discard(e)
                adj[e].discard(a)
                adj[c].discard(b)
                adj[b].discard(c)
                adj[a].add(b)
                adj[b].add(a)
                adj[c].add(e)
                adj[e].add(c)
    return adj


def _grow(n, edges, d, D, deadline, rng, moore):
    adj = _to_adj(n, edges)
    side = _bipartition(n, adj)
    best = (n, list(edges))
    while time.monotonic() < deadline and n + 2 <= moore:
        now = time.monotonic()
        end = min(deadline, now + max(2.0, 0.5 * (deadline - now)))
        nadj = [set(s) for s in adj] + [set(), set()]
        nside = side + [0, 1]
        x, y = n, n + 1
        sp1 = [v for v in range(n) if side[v] == 1 and len(nadj[v]) < d]
        sp0 = [v for v in range(n) if side[v] == 0 and len(nadj[v]) < d]
        rng.shuffle(sp1)
        rng.shuffle(sp0)
        for v in sp1[:d]:
            nadj[x].add(v)
            nadj[v].add(x)
        for v in sp0[:d]:
            nadj[y].add(v)
            nadj[v].add(y)
        res = _anneal(n + 2, nadj, nside, d, D, rng, end)
        if res is None:
            continue
        n, adj, side = n + 2, res, nside
        e = _edges_of(n, adj)
        if not lib.is_valid(n, e, d, D):
            break
        best = (n, e)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.3 * time_limit, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = (fb_n, fb_e)
    best_n = fb_n

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2 and D >= 3:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        L = 2 * D
        consider(L, [(i, (i + 1) % L) for i in range(L)])

    moore = lib._moore_bound(d, D)

    if D >= 3 and d >= 3:
        arc_deadline = start + 0.3 * budget
        for q in range(min(d - 1, 31), 1, -1):
            if not lib.is_prime_power(q):
                continue
            m, edges, pl, lp, index = _pg_structure(q)
            consider(2 * m, edges)  # PG(2,q) incidence, degree q+1 <= d
            s = d - q - 1
            if s < 1:
                continue
            cands = []
            if s >= 2:
                cs = _conic(q, index)
                if _loads_ok(cs, s, m, pl, lp):
                    cands.append(cs)
            gr = _greedy(m, s, pl, lp, rng, 60, arc_deadline)
            if gr and _loads_ok(gr, s, m, pl, lp):
                cands.append(gr)
            for S in cands:
                n2, e2 = _arc_graph(m, edges, pl, lp, S)
                consider(n2, e2)

        # Grow the best graph found by annealed repair.
        if best_n + 2 <= moore and time.monotonic() < deadline:
            n1, e1 = _grow(best_n, best[1], d, D, deadline, rng, moore)
            consider(n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fb_n, fb_e)
    return best
