import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3). Safe baseline.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
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


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, pl, lp, rng, 40, deadline)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if len(cs) > len(S) and _loads_ok(cs, s, m, pl, lp):
                S = cs
        if S and not _loads_ok(S, s, m, pl, lp):
            S = []
        out.append(_arc_graph(m, edges, pl, lp, S))
    out.sort(key=lambda t: -t[0])
    return out


# ----------------------------------------------------------------------------
# Bold step: add one vertex per side to a near-extremal base and anneal the
# edges (rewire / add) until the bipartite graph has diameter <= D.
# Cost = number of ordered vertex pairs at distance > D (zero means valid).
# ----------------------------------------------------------------------------

def _two_color(n, adj):
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


def _bad(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(n - r.bit_count() for r in reach)


def _anneal(n0, e0, d, D, deadline, rng):
    n = n0 + 2
    adj = [set() for _ in range(n)]
    for u, v in e0:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n0, adj)
    color += [0, 1]  # new A-vertex (side 0) and new B-vertex (side 1)
    L0 = [v for v in range(n) if color[v] == 0]
    L1 = [v for v in range(n) if color[v] == 1]
    deg = [len(s) for s in adj]
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in e0]

    def add_edge(x, y):
        a, b = (x, y) if color[x] == 0 else (y, x)
        adj[a].add(b)
        adj[b].add(a)
        deg[a] += 1
        deg[b] += 1
        E.append((a, b))

    def remove_last():
        a, b = E.pop()
        adj[a].discard(b)
        adj[b].discard(a)
        deg[a] -= 1
        deg[b] -= 1

    def set_edge(i, na, nb):
        a, b = E[i]
        adj[a].discard(b)
        adj[b].discard(a)
        deg[a] -= 1
        deg[b] -= 1
        adj[na].add(nb)
        adj[nb].add(na)
        deg[na] += 1
        deg[nb] += 1
        E[i] = (na, nb)

    # Attach the two new vertices to spare opposite-side vertices.
    for x in (n0, n0 + 1):
        targets = L1 if color[x] == 0 else L0
        tries = 0
        while deg[x] < d and tries < 2000:
            tries += 1
            y = rng.choice(targets)
            if deg[y] >= d or y in adj[x]:
                continue
            add_edge(x, y)

    cur = _bad(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = 30.0 * (0.5 / 30.0) ** frac
        if rng.random() < 0.3:
            a = rng.choice(L0)
            b = rng.choice(L1)
            if deg[a] >= d or deg[b] >= d or b in adj[a]:
                continue
            add_edge(a, b)
            new = _bad(n, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                remove_last()
        else:
            i = rng.randrange(len(E))
            a, b = E[i]
            if rng.random() < 0.5:
                w = rng.choice(L1)
                if w == b or w in adj[a] or deg[w] >= d:
                    continue
                set_edge(i, a, w)
                new = _bad(n, adj, D)
                if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                    cur = new
                else:
                    set_edge(i, a, b)
            else:
                w = rng.choice(L0)
                if w == a or w in adj[b] or deg[w] >= d:
                    continue
                set_edge(i, w, b)
                new = _bad(n, adj, D)
                if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                    cur = new
                else:
                    set_edge(i, a, b)

    if cur == 0:
        return n, [(u, v) for u, v in E]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    if D >= 3:
        cands = _arc_candidates(d, start + 0.15 * time_limit, rng)
        base = None
        for n_c, e_c in cands:
            if n_c <= best_n:
                break
            if lib.is_valid(n_c, e_c, d, D):
                base = (n_c, e_c)
                break
        if base is not None:
            if base[0] > best_n:
                best_n, best_e = base
        if base is not None or D >= 3:
            bn, be = (base if base is not None else (best_n, best_e))
            res = _anneal(bn, be, d, D, deadline, rng)
            if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
                best_n, best_e = res

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
