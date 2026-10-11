import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (diameter 3 records and projective planes).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Helpers on adjacency-list graphs.
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (bitmask ball expansion)."""
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


# ----------------------------------------------------------------------------
# New idea: grow by vertex insertion with edge stealing, then repair by
# annealed endpoint rewiring under the bad-pair objective.
#
# Insertion: a new vertex x on side c takes d opposite-side neighbours. Spare
# degree is used first; full neighbours give up one random edge (its other
# endpoint becomes deficient). The resulting graph is repaired by simulated
# annealing that moves one endpoint of an edge to another vertex of the
# same side, minimising the number of pairs at distance > D. Finally the
# leftover spare degree is saturated with edges, which never hurts diameter.
# ----------------------------------------------------------------------------

def _saturate(n, adj, color, d, rng):
    """Greedily join deficient opposite-side vertices (adding edges keeps diameter <= D)."""
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].append(b)
            adj[b].append(a)


def _insert_vertex(n, adj, color, d, rng, c):
    """Add a vertex of side c adjacent to d opposite-side vertices; returns new vertex count."""
    opp = [v for v in range(n) if color[v] != c]
    rng.shuffle(opp)
    chosen = [v for v in opp if len(adj[v]) < d][:d]
    if len(chosen) < d:
        full = [v for v in opp if len(adj[v]) >= d]
        for b in full[: d - len(chosen)]:
            a = rng.choice(adj[b])
            adj[b].remove(a)
            adj[a].remove(b)
            chosen.append(b)
    adj.append([])
    color.append(c)
    x = n
    for b in chosen:
        adj[x].append(b)
        adj[b].append(x)
    return n + 1


def _anneal(n, adj, color, d, D, rng, deadline, iters, T0=0.5):
    """Annealed endpoint rewiring; returns True iff the graph reaches diameter <= D."""
    cost = _bad_pairs(n, adj, D)
    if cost == 0:
        return True
    sides = [[v for v in range(n) if color[v] == c] for c in (0, 1)]
    it = 0
    while cost > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        T = T0 * (0.02 ** (it / iters))
        a = rng.randrange(n)
        if not adj[a]:
            continue
        b = rng.choice(adj[a])
        if rng.random() < 0.5:
            keep, moved = a, b
        else:
            keep, moved = b, a
        pool = sides[color[moved]]
        c = None
        for _ in range(30):
            x = pool[rng.randrange(len(pool))]
            if x != moved and len(adj[x]) < d and x not in adj[keep]:
                c = x
                break
        if c is None:
            continue
        adj[keep].remove(moved)
        adj[moved].remove(keep)
        adj[keep].append(c)
        adj[c].append(keep)
        new = _bad_pairs(n, adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            adj[keep].remove(c)
            adj[c].remove(keep)
            adj[keep].append(moved)
            adj[moved].append(keep)
    return cost == 0


def _grow(n, adj, color, d, D, deadline, rng, limit_n):
    """Repeatedly insert one vertex and repair; keeps the largest valid graph reached."""
    best = ([list(a) for a in adj], list(color), n)
    while time.monotonic() < deadline and best[2] < limit_n:
        cur_adj = [list(a) for a in best[0]]
        cur_color = list(best[1])
        cur_n = _insert_vertex(best[2], cur_adj, cur_color, d, rng, rng.randrange(2))
        if _anneal(cur_n, cur_adj, cur_color, d, D, rng, deadline, iters=1000):
            _saturate(cur_n, cur_adj, cur_color, d, rng)
            best = (cur_adj, cur_color, cur_n)
    return best[2], best[0]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

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
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        limit_n = lib._moore_bound(d, D)
        if best_n < limit_n:
            n0 = best_n
            adj0 = _to_adj(n0, best[1])
            color0 = _bipartition(n0, adj0)
            gn, gadj = _grow(n0, adj0, color0, d, D, deadline, rng, limit_n)
            ge = [(u, v) for u in range(gn) for v in gadj[u] if u < v]
            consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
