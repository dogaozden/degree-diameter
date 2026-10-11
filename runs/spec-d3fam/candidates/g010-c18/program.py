import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: Araujo-Pardo & Lopez record (d = q+2, q prime power) and
# the plain projective plane incidence graph as fallbacks.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree q+2) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


# ----------------------------------------------------------------------------
# Helpers for the graph-state search.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a graph given by adjacency sets/lists (components coloured independently)."""
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
    """Number of unordered vertex pairs at distance > D (unreachable counts), via bitmask balls."""
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


# ----------------------------------------------------------------------------
# NEW IDEA: degree-preserving "double-steal" growth.
#
# To add two vertices x (side 0) and y (side 1) to a graph in which every
# vertex is already saturated, choose a matching of d-1 edges (a_i, b_i) with
# distinct a_i and distinct b_i. Replace each (a_i, b_i) by (x, b_i) and
# (a_i, y), and add the edge (x, y). Every old vertex keeps its degree, x and y
# reach degree d, and the graph stays bipartite. The result has two more
# vertices, and a degree-preserving edge-switch search then repairs the
# diameter.
# ----------------------------------------------------------------------------

def _grow_pair(n, adj, color, eds, eset, d, rng):
    """Apply one double-steal insertion in place. Returns the new vertex count, or None."""
    order = list(range(len(eds)))
    rng.shuffle(order)
    ua, ub, chosen = set(), set(), []
    for idx in order:
        a, b = eds[idx]
        if a in ua or b in ub:
            continue
        ua.add(a)
        ub.add(b)
        chosen.append(idx)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    x, y = n, n + 1
    adj.append(set())
    adj.append(set())
    color.append(0)
    color.append(1)
    for idx in chosen:
        a, b = eds[idx]
        eset.discard((a, b))
        adj[a].discard(b)
        adj[b].discard(a)
        eds[idx] = [x, b]
        eset.add((x, b))
        adj[x].add(b)
        adj[b].add(x)
        eds.append([a, y])
        eset.add((a, y))
        adj[a].add(y)
        adj[y].add(a)
    eds.append([x, y])
    eset.add((x, y))
    adj[x].add(y)
    adj[y].add(x)
    return n + 2


# ----------------------------------------------------------------------------
# Degree-preserving 2-switch annealing: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
# Keeps every degree and the bipartition; minimises the bad-pair count.
# ----------------------------------------------------------------------------

def _anneal(n, adj, eds, eset, D, deadline, rng):
    """Anneal toward zero bad pairs. Returns True if the state reached diameter <= D."""
    cur = _bad_pairs(n, adj, D)
    m = len(eds)
    if cur == 0:
        return True
    if m < 2:
        return False

    def reset(i, a, b):
        oa, ob = eds[i]
        eset.discard((oa, ob))
        adj[oa].discard(ob)
        adj[ob].discard(oa)
        eds[i] = [a, b]
        eset.add((a, b))
        adj[a].add(b)
        adj[b].add(a)

    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0, T1 = 1.0, 0.05
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = eds[i]
        a2, b2 = eds[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        reset(i, a1, b2)
        reset(j, a2, b1)
        new = _bad_pairs(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            reset(j, a2, b2)
            reset(i, a1, b1)
    return cur == 0


def _grow_repair(n, edges, d, D, deadline, rng):
    """Repeatedly grow by double-steal insertion, repairing the diameter each time.

    Returns the largest valid (n, edges) reached. Each attempt works on copies, so a
    failed attempt leaves the last valid graph untouched.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, adj)
    for u, v in edges:
        if color[u] == color[v]:
            return n, list(edges)
    eds, eset = [], set()
    for u, v in edges:
        a, b = (u, v) if color[u] == 0 else (v, u)
        eds.append([a, b])
        eset.add((a, b))
    best = (n, list(edges))
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        budget = 0.5 * remaining
        adj2 = [set(s) for s in adj]
        eds2 = [list(e) for e in eds]
        eset2 = set(eset)
        color2 = list(color)
        nn = _grow_pair(n, adj2, color2, eds2, eset2, d, rng)
        if nn is None:
            break
        if not _anneal(nn, adj2, eds2, eset2, D, time.monotonic() + budget, rng):
            break
        n, adj, eds, eset, color = nn, adj2, eds2, eset2, color2
        best = (n, [(a, b) for a, b in eds])
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    # Growth search: start from the best valid graph and add double-steal pairs.
    if D >= 3 and d >= 5:
        n1, e1 = _grow_repair(best_n, best[1], d, D, deadline, rng)
        consider(n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
