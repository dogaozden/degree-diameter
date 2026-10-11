import math
import random
import time
import itertools

import lib


# ----------------------------------------------------------------------------
# Algebraic bases (diameter 3): Araujo-Pardo-Lopez graph and projective planes.
# ----------------------------------------------------------------------------

def _araujo_best(d):
    """Araujo-Pardo-Lopez graph for the largest prime power q <= d - 2 (degree q + 2 <= d)."""
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except ValueError:
                return None
    return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _arc_extensions(d, deadline, rng):
    """Candidates from PG(2, q) with extra vertices attached to an arc of spare-degree points."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices (only shortens distances)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
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
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# New construction: vertex-transitive Haar graphs H(Z_m, S) with |S| = d.
#
# Vertices a_i and b_j; a_i ~ b_{i+s} for s in S. Shift invariance means
# dist(a_i, b_j) = dist(a_0, b_{j-i}) and dist(a_i, a_k) = dist(a_0, a_{k-i}),
# so a single BFS from a_0 certifies the whole diameter. The search is a
# plateau-accepting hill climb over the connection set S (0 is WLOG in S).
# ----------------------------------------------------------------------------

def _haar_cost(m, S, D):
    """Vertices (out of 2m) not within distance D of a_0. Zero iff diameter <= D."""
    seen_a = {0}
    seen_b = set()
    fa = [0]
    fb = []
    for step in range(D):
        if step % 2 == 0:
            nxt = []
            for i in fa:
                for s in S:
                    j = (i + s) % m
                    if j not in seen_b:
                        seen_b.add(j)
                        nxt.append(j)
            fb = nxt
        else:
            nxt = []
            for j in fb:
                for s in S:
                    i = (j - s) % m
                    if i not in seen_a:
                        seen_a.add(i)
                        nxt.append(i)
            fa = nxt
    return 2 * m - len(seen_a) - len(seen_b)


def _haar_search(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None
    S = [0] + rng.sample(others, d - 1)
    c = _haar_cost(m, S, D)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _haar_cost(m, T, D)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
        return best_n

    T = time_limit

    # Algebraic bases for D >= 3.
    if D >= 3 and best_n < moore:
        ara = _araujo_best(d)
        if ara is not None:
            consider(ara[0], ara[1])
            consider(ara[0], _saturate_edges(ara[0], ara[1], d, rng))
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            consider(pg[0], _saturate_edges(pg[0], pg[1], d, rng))
        for n_c, e_c in _arc_extensions(d, start + 0.3 * T, random.Random(seed * 7919 + d)):
            consider(n_c, _saturate_edges(n_c, e_c, d, rng))

    # Bold new phase: search vertex-transitive Haar graphs of growing order.
    # Each attempt targets an order just above the current best.
    if D >= 3 and d >= 3:
        while time.monotonic() < deadline - 0.2 and best_n < moore:
            now = time.monotonic()
            remaining = deadline - now
            slice_end = min(deadline, now + max(1.5, 0.15 * remaining))
            m = best_n // 2 + 1 + rng.randrange(0, 4)
            if m < d:
                m = d
            S = _haar_search(d, D, m, rng, slice_end, 4000)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
