import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Seed graphs: K_{d,d}, the projective plane PG(2,q), and the quadrangle W(q).
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
    edges = []
    nl = 0
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
            for p in L:
                edges.append((p, P + nl))
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nl += 1
    return 2 * P, edges


def _seeds(d, D):
    """Valid seed graphs, largest first."""
    out = [lib.haar_graph(d, range(d))]
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                out.append(lib.projective_plane_incidence(q))
                break
    if D >= 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    valid = [g for g in out if lib.is_valid(g[0], g[1], d, D)]
    valid.sort(key=lambda g: -g[0])
    return valid


# ----------------------------------------------------------------------------
# Edge-level annealing on a bipartite graph with growing order.
#
# State: adjacency sets, a side label per vertex, and the two side lists.
# Moves: 2-switches (keep degrees and bipartiteness) with Metropolis acceptance
# on the number of ordered pairs at distance > D. When the cost hits zero the
# graph is valid, so it is recorded and grown by splitting a random edge into
# two new vertices of opposite sides. Saturation then uses spare degree.
# ----------------------------------------------------------------------------

def _bipart(n, adj):
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
    """Ordered pairs at distance > D (zero means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _edge_list(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _saturate(adj, d, A, B, rng):
    la = [a for a in A if len(adj[a]) < d]
    lb = [b for b in B if len(adj[b]) < d]
    pairs = [(a, b) for a in la for b in lb if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].add(b)
            adj[b].add(a)


def _rewire(adj, a1, b1, a2, b2):
    """Replace edges a1-b1, a2-b2 by a1-b2, a2-b1."""
    adj[a1].remove(b1)
    adj[b1].remove(a1)
    adj[a2].remove(b2)
    adj[b2].remove(a2)
    adj[a1].add(b2)
    adj[b2].add(a1)
    adj[a2].add(b1)
    adj[b1].add(a2)


def _switch(adj, A, rng):
    """Propose a random 2-switch; apply it and return its tuple, or None if not applicable."""
    a1 = rng.choice(A)
    if not adj[a1]:
        return None
    b1 = rng.choice(tuple(adj[a1]))
    a2 = rng.choice(A)
    if a2 == a1 or not adj[a2]:
        return None
    b2 = rng.choice(tuple(adj[a2]))
    if b2 == b1 or b2 in adj[a1] or b1 in adj[a2]:
        return None
    _rewire(adj, a1, b1, a2, b2)
    return (a1, b1, a2, b2)


def _grow(adj, side, A, B, rng):
    """Insert a new A-vertex x and B-vertex y by splitting a random edge a2-b2."""
    a2 = None
    for _ in range(200):
        cand = rng.choice(A)
        if adj[cand]:
            a2 = cand
            break
    if a2 is None:
        return
    b2 = rng.choice(tuple(adj[a2]))
    x = len(adj)
    y = x + 1
    adj.append(set())
    adj.append(set())
    side.append(0)
    side.append(1)
    A.append(x)
    B.append(y)
    adj[a2].discard(b2)
    adj[b2].discard(a2)
    adj[a2].add(y)
    adj[y].add(a2)
    adj[b2].add(x)
    adj[x].add(b2)
    adj[x].add(y)
    adj[y].add(x)


def _search(n, edges, d, D, deadline, rng):
    moore = lib.moore_bound(d, D)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    side = _bipart(n, adj)
    A = [v for v in range(n) if side[v] == 0]
    B = [v for v in range(n) if side[v] == 1]
    best_n, best_e = n, list(edges)
    _saturate(adj, d, A, B, rng)
    cur = _bad(len(adj), adj, D)
    zero = None
    stag = 0
    best_cur = cur
    T = 1.5

    while time.monotonic() < deadline:
        n = len(adj)
        if cur == 0:
            if n > best_n:
                best_n, best_e = n, _edge_list(adj)
            if n >= moore:
                break
            zero = ([set(s) for s in adj], list(side), list(A), list(B))
            _grow(adj, side, A, B, rng)
            _saturate(adj, d, A, B, rng)
            cur = _bad(len(adj), adj, D)
            stag = 0
            best_cur = cur
            continue

        for _ in range(100):
            mv = _switch(adj, A, rng)
            if mv is None:
                continue
            a1, b1, a2, b2 = mv
            c2 = _bad(n, adj, D)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
            else:
                _rewire(adj, a1, b2, a2, b1)
            if cur == 0:
                break
        stag += 100
        if cur < best_cur:
            best_cur = cur
            stag = 0
        if stag > 2000 and zero is not None:
            zadj, zside, zA, zB = zero
            adj = [set(s) for s in zadj]
            side = list(zside)
            A = list(zA)
            B = list(zB)
            for _ in range(6):
                _switch(adj, A, rng)
            cur = _bad(len(adj), adj, D)
            stag = 0
            best_cur = cur
    return best_n, best_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d <= 0:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    seeds = _seeds(d, D)
    best_n, best_e = seeds[0]

    if d >= 3 and best_n < lib.moore_bound(d, D) and time.monotonic() < deadline:
        n2, e2 = _search(best_n, best_e, d, D, deadline, rng)
        if n2 > best_n and lib.is_valid(n2, e2, d, D):
            best_n, best_e = n2, e2

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
