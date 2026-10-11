import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic starting points.
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 9 for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Edge-swap surgery with vertex addition (new family for D >= 3).
#
# Move: pick t = d-1 disjoint edges (a_i, b_i), a_i on side 0, b_i on side 1.
# Remove them, add x on side 1 joined to all a_i, and y on side 0 joined to all
# b_i, plus the edge x-y. Every old vertex keeps its degree and x, y reach degree d.
# The move is accepted by annealing on the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D, via bitmask balls."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(n - b.bit_count() for b in ball) // 2


def _try_move(adj, color, n, t, rng):
    """Remove a random matching of size t and add two vertices. Returns the removed pairs or None."""
    side0 = [v for v in range(n) if color[v] == 0]
    pairs = []
    usedA, usedB = set(), set()
    for _ in range(400):
        if len(pairs) == t:
            break
        a = rng.choice(side0)
        if a in usedA or not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        if b in usedB:
            continue
        pairs.append((a, b))
        usedA.add(a)
        usedB.add(b)
    if len(pairs) < t:
        return None
    x, y = n, n + 1
    adj.append(set())
    adj.append(set())
    color.append(1)
    color.append(0)
    for a, b in pairs:
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(x)
        adj[x].add(a)
        adj[b].add(y)
        adj[y].add(b)
    adj[x].add(y)
    adj[y].add(x)
    return pairs


def _undo_move(adj, color, pairs, n_old):
    """Revert a move made by _try_move, given the old vertex count."""
    x, y = n_old, n_old + 1
    for a in list(adj[x]):
        adj[a].discard(x)
    for b in list(adj[y]):
        adj[b].discard(y)
    for a, b in pairs:
        adj[a].add(b)
        adj[b].add(a)
    del adj[n_old:]
    del color[n_old:]


def _to_edges(adj, n):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _fill(E, n, d, color, rng):
    """Greedily add edges between deficient opposite-side vertices (never increases distances)."""
    existing = set((min(u, v), max(u, v)) for u, v in E)
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    out = list(E)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return out


def _surgery(n0, edges0, d, D, deadline, rng):
    """Anneal edge-swap surgery from a start graph. Returns (n, edges) with cost 0, or None."""
    if d - 1 < 1:
        return None
    n = n0
    color = [0] * (n0 // 2) + [1] * (n0 - n0 // 2)
    adj = [set() for _ in range(n)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)

    cur = _bad(n, adj, D)
    raw = None  # (n, edges, colors) for the largest zero-cost state seen
    if cur == 0:
        raw = (n, list(edges0), list(color))

    t = d - 1
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = max(0.08, 1.2 * (1.0 - frac))
        n_old = n
        pairs = _try_move(adj, color, n, t, rng)
        if pairs is None:
            continue
        n = n_old + 2
        new = _bad(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cur = new
            if cur == 0 and (raw is None or n > raw[0]):
                raw = (n, _to_edges(adj, n), list(color))
        else:
            _undo_move(adj, color, pairs, n_old)
            n = n_old

    if raw is None:
        return None
    rn, re, rcol = raw
    filled = _fill(re, rn, d, rcol, rng)
    if lib.is_valid(rn, filled, d, D):
        return rn, filled
    return rn, re


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    seed_graph = None
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            seed_graph = pg
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
            if seed_graph is None or ar[0] > seed_graph[0]:
                seed_graph = ar
    else:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            seed_graph = gq

    # New main search: edge-swap surgery with vertex addition from the algebraic seed.
    if seed_graph is not None and d >= 3:
        res = _surgery(seed_graph[0], seed_graph[1], d, D, deadline, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
