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
# New helper: degree-preserving pair insertion followed by edge-switch annealing.
#
# Insert two new vertices A (side 0) and B (side 1) into a bipartite graph whose
# degrees are already near d. Pick up to d edges (a_i, b_i) with distinct
# endpoints, delete them, and add A-b_i and a_i-B. Every old vertex keeps its
# degree, A and B get degree d, and the vertex count grows by 2.
#
# The diameter defect is then repaired by double-edge switches
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). These keep all degrees and the bipartition,
# and Metropolis acceptance uses the exact count of vertex pairs farther than D.
# ----------------------------------------------------------------------------

def _adj_lists(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitmask BFS)."""
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


def _insert_pair(n, edges, color, d, rng):
    """Add two vertices (side 0 and side 1) by rewiring up to d edges; degrees of old vertices are kept."""
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    order = list(range(len(E)))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), set()
    for idx in order:
        if len(chosen) >= d:
            break
        a, b = E[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.add(idx)
    A, B = n, n + 1
    out = [E[i] for i in range(len(E)) if i not in chosen]
    for idx in chosen:
        a, b = E[idx]
        out.append((A, b))
        out.append((a, B))
    return n + 2, out, color + [0, 1]


def _swap(adj, a1, b1, a2, b2, fwd):
    """Switch (a1,b1),(a2,b2) into (a1,b2),(a2,b1) if fwd, else undo it."""
    if fwd:
        old = [(a1, b1), (a2, b2)]
        new = [(a1, b2), (a2, b1)]
    else:
        old = [(a1, b2), (a2, b1)]
        new = [(a1, b1), (a2, b2)]
    for a, b in old:
        adj[a].discard(b)
        adj[b].discard(a)
    for a, b in new:
        adj[a].add(b)
        adj[b].add(a)


def _anneal_switch(n, E, D, deadline, t0, rng):
    """Edge-switch annealing; returns oriented edge list with zero defect, or None."""
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    E = [list(e) for e in E]
    cost = _bad_count(n, adj, D)
    span = max(1e-6, deadline - t0)
    m = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 1.0 * (0.03 ** ((now - t0) / span))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if b2 in adj[a1] or b1 in adj[a2]:
            continue
        _swap(adj, a1, b1, a2, b2, True)
        c2 = _bad_count(n, adj, D)
        if c2 <= cost - T * math.log(1.0 - rng.random()):
            E[i] = [a1, b2]
            E[j] = [a2, b1]
            cost = c2
        else:
            _swap(adj, a1, b1, a2, b2, False)
    return [tuple(e) for e in E]


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

        # Pair insertion plus switch annealing, chained while it keeps succeeding.
        cur_n, cur_e = best_n, list(best[1])
        cur_color = _bipartition(cur_n, _adj_lists(cur_n, cur_e))
        attempt_budget = 0.4 * time_limit
        while time.monotonic() < deadline:
            t0 = time.monotonic()
            attempt_deadline = min(deadline, t0 + attempt_budget)
            n2, e2, c2 = _insert_pair(cur_n, cur_e, cur_color, d, rng)
            res = _anneal_switch(n2, e2, D, attempt_deadline, t0, rng)
            if res is not None:
                cur_n, cur_e, cur_color = n2, list(res), c2
                consider(n2, res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
