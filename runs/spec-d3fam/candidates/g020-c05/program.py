import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline constructions (safe fallbacks).
# ----------------------------------------------------------------------------

def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree q+2, diameter 3) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bold alternative: direct annealing on bipartite graphs with a degree cap.
#
# Instead of algebra, start from a valid diameter-3 graph on n vertices, add one
# vertex to each side, and search over edge sets (degree <= d, bipartite) for a
# graph of diameter <= 3. Moves: remove an edge and refill, degree-preserving
# 2-switches, and adding an edge between two deficient opposite vertices.
# Cost = (number of pairs at distance > D) + 0.5 * (total degree deficiency).
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D, via bitmask ball expansion."""
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


def _relabel_bipartite(n, edges):
    """Relabel so side A is 0..na-1 and side B is na..; add one fresh vertex per side.

    Returns (new_n, na, edges) with new_n = n + 2 for a connected bipartite input.
    """
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    idx = {}
    for i, v in enumerate(A):
        idx[v] = i
    na = len(A) + 1  # slot for the new A-vertex
    for j, v in enumerate(B):
        idx[v] = na + j
    new_n = na + len(B) + 1  # slot for the new B-vertex
    E = []
    for u, v in edges:
        x, y = idx[u], idx[v]
        E.append((min(x, y), max(x, y)))
    return new_n, na, E


def _search_step(n, na, edges, d, D, deadline, rng):
    """Anneal an edge set on n vertices (A = 0..na-1, B = na..n-1) to reach diameter <= D.

    Returns the edge list on success, or None if the deadline passes first.
    """
    adj = [set() for _ in range(n)]
    elist = []
    epos = {}

    def _add(a, b):
        adj[a].add(b)
        adj[b].add(a)
        epos[(a, b)] = len(elist)
        elist.append((a, b))

    def _rem(a, b):
        adj[a].discard(b)
        adj[b].discard(a)
        idx = epos.pop((a, b))
        last = elist.pop()
        if idx < len(elist):
            elist[idx] = last
            epos[last] = idx

    def _def():
        return sum(d - len(s) for s in adj)

    for a, b in edges:
        _add(a, b)
    # Greedy initial fill of spare degree between opposite sides.
    for a in range(na):
        for b in range(na, n):
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                _add(a, b)

    bad = _bad_pairs(n, adj, D)
    if bad == 0:
        return list(elist)
    cur = bad + 0.5 * _def()
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = max(0.05, 1.5 * (1.0 - frac))
        log = []
        r = rng.random()
        if r < 0.4 and elist:
            a, b = elist[rng.randrange(len(elist))]
            _rem(a, b)
            log.append((0, a, b))
            for _ in range(30):
                x = rng.randrange(na)
                y = rng.randrange(na, n)
                if len(adj[x]) < d and len(adj[y]) < d and y not in adj[x]:
                    _add(x, y)
                    log.append((1, x, y))
                    break
        elif r < 0.85 and len(elist) >= 2:
            (a1, b1), (a2, b2) = rng.sample(elist, 2)
            if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            _rem(a1, b1)
            _rem(a2, b2)
            _add(a1, b2)
            _add(a2, b1)
            log.extend([(0, a1, b1), (0, a2, b2), (1, a1, b2), (1, a2, b1)])
        else:
            for _ in range(30):
                x = rng.randrange(na)
                y = rng.randrange(na, n)
                if len(adj[x]) < d and len(adj[y]) < d and y not in adj[x]:
                    _add(x, y)
                    log.append((1, x, y))
                    break

        nb = _bad_pairs(n, adj, D)
        new = nb + 0.5 * _def()
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            bad = nb
            if bad == 0:
                return list(elist)
        else:
            for op, a, b in reversed(log):
                if op == 1:
                    _rem(a, b)
                else:
                    _add(a, b)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        rec = _araujo(d)
        if rec is not None:
            consider(rec[0], rec[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 3 and best_n > 2:
        # Bold path: grow the best valid graph by two vertices at a time using
        # direct annealing over edge sets. Each success becomes the new base.
        cur_n, cur_e = best
        while time.monotonic() < deadline:
            cn, na, E = _relabel_bipartite(cur_n, cur_e)
            res = _search_step(cn, na, E, d, D, deadline, rng)
            if res is None:
                break
            if not lib.is_valid(cn, res, d, D):
                break
            cur_n, cur_e = cn, res
            consider(cur_n, cur_e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
