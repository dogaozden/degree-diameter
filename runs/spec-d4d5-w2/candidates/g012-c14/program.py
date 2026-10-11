import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe base constructions: K_{d,d}, projective plane incidence, and W(q).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _base_candidates(d, D):
    yield lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                yield lib.projective_plane_incidence(q)
                break
    if D >= 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                yield _gq_w(q)
                break


# ----------------------------------------------------------------------------
# Direct search on bipartite graphs with degree <= d and diameter <= D.
#
# Start from a valid base graph, add one A and one B vertex at a time, and
# repair with annealing over three moves: add an edge, delete an edge, or
# 2-switch two edges (which keeps every degree fixed). Cost is the number of
# unordered vertex pairs at distance more than D. Each grow step is accepted
# only after the cost reaches zero, and every result is checked by lib.is_valid.
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
    """Number of unordered pairs at distance more than D, via bitmask balls."""
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


def _grow_anneal(d, D, n, edges, deadline, rng):
    col = _two_colour(n, edges)
    E = [(u, v) if col[u] == 0 else (v, u) for u, v in edges]
    S = set(E)
    adj = [set() for _ in range(n)]
    deg = [0] * n
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
        deg[a] += 1
        deg[b] += 1
    best = None

    def link(e):
        a, b = e
        adj[a].add(b)
        adj[b].add(a)
        deg[a] += 1
        deg[b] += 1

    def unlink(e):
        a, b = e
        adj[a].discard(b)
        adj[b].discard(a)
        deg[a] -= 1
        deg[b] -= 1

    while time.monotonic() < deadline:
        cost = _bad(n, adj, D)
        if cost == 0:
            if not lib.is_valid(n, E, d, D):
                break
            best = (n, list(E))
            # Grow by one A vertex and one B vertex (isolated until repaired).
            col.extend([0, 1])
            adj.extend([set(), set()])
            deg.extend([0, 0])
            n += 2
            continue

        t0 = time.monotonic()
        span = max(1e-3, deadline - t0)
        T0 = 0.1 * cost + 0.5
        while cost > 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = max(1e-6, T0 * (0.02 ** ((now - t0) / span)))
            r = rng.random()

            if r < 0.3:
                # Add an edge between a deficient A vertex and a deficient B vertex.
                a = rng.randrange(n)
                b = rng.randrange(n)
                if (col[a] == 0 and col[b] == 1 and deg[a] < d and deg[b] < d
                        and b not in adj[a]):
                    e = (a, b)
                    E.append(e)
                    S.add(e)
                    link(e)
                    new = _bad(n, adj, D)
                    delta = new - cost
                    if delta <= 0 or rng.random() < math.exp(-delta / T):
                        cost = new
                    else:
                        unlink(e)
                        S.discard(e)
                        E.pop()

            elif r < 0.4:
                # Delete a random edge.
                if E:
                    i = rng.randrange(len(E))
                    e = E[i]
                    E[i] = E[-1]
                    E.pop()
                    S.discard(e)
                    unlink(e)
                    new = _bad(n, adj, D)
                    delta = new - cost
                    if delta <= 0 or rng.random() < math.exp(-delta / T):
                        cost = new
                    else:
                        link(e)
                        S.add(e)
                        E.append(e)

            else:
                # 2-switch: (a,b),(c,f) -> (a,f),(c,b). Degrees are preserved.
                if len(E) >= 2:
                    i = rng.randrange(len(E))
                    j = rng.randrange(len(E))
                    if i != j:
                        a, b = E[i]
                        c, f = E[j]
                        if a != c and b != f:
                            n1 = (a, f)
                            n2 = (c, b)
                            if n1 not in S and n2 not in S:
                                unlink((a, b))
                                unlink((c, f))
                                link(n1)
                                link(n2)
                                S.discard((a, b))
                                S.discard((c, f))
                                S.add(n1)
                                S.add(n2)
                                E[i] = n1
                                E[j] = n2
                                new = _bad(n, adj, D)
                                delta = new - cost
                                if delta <= 0 or rng.random() < math.exp(-delta / T):
                                    cost = new
                                else:
                                    unlink(n1)
                                    unlink(n2)
                                    link((a, b))
                                    link((c, f))
                                    S.discard(n1)
                                    S.discard(n2)
                                    S.add((a, b))
                                    S.add((c, f))
                                    E[i] = (a, b)
                                    E[j] = (c, f)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = None
    for n, e in _base_candidates(d, D):
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)
    if best is None:
        best = lib.haar_graph(d, range(d))

    # Direct annealed growth. It only runs where the Moore bound leaves room
    # above the base, so calibration cases such as d3D3 return immediately.
    if d >= 3 and D >= 4 and best[0] < lib.moore_bound(d, D):
        res = _grow_anneal(d, D, best[0], best[1], deadline, rng)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
