import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (diameter 3 records and incidence graphs).
# ----------------------------------------------------------------------------

def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bold alternative: grow by two vertices, then repair by degree-preserving
# double-edge swaps under simulated annealing.
#
# Augmentation: pick d-1 edges (a_i, b_i) forming a matching. Delete them, add
# a new A-vertex x adjacent to every b_i and a new B-vertex y adjacent to every
# a_i, plus the edge x-y. Every degree stays at most d and the graph stays
# bipartite. The new graph has 2 more vertices, typically with diameter
# violations, which the annealing removes by rewiring. Every accepted result
# is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

ATT = 5.0  # seconds per augmentation attempt


def _orient(n, edges):
    """Return edges as (a, b) pairs with a on colour class 0, or None if not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    out = []
    for u, v in edges:
        out.append((u, v) if color[u] == 0 else (v, u))
    return out


def _ball_cost(n, adj, D):
    """Number of unordered pairs at distance > D (zero iff diameter <= D)."""
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


def _augment(n, E, d, rng):
    """Add two vertices x (side A) and y (side B) using d-1 matched edges; degrees stay <= d."""
    if d < 2:
        return None
    idx = list(range(len(E)))
    rng.shuffle(idx)
    used_a, used_b, chosen = set(), set(), []
    for i in idx:
        a, b = E[i]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(i)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    x, y = n, n + 1
    cs = set(chosen)
    out = [tuple(E[k]) for k in range(len(E)) if k not in cs]
    for i in chosen:
        a, b = E[i]
        out.append((x, b))
        out.append((a, y))
    out.append((x, y))
    return n + 2, out


def _anneal(n, E0, D, rng, end):
    """Repair diameter with degree-preserving double-edge swaps; returns edges or None."""
    E = [list(e) for e in E0]
    m = len(E)
    adj = [set() for _ in range(n)]
    S = set()
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
        S.add((a, b))
    cost = _ball_cost(n, adj, D)
    t0 = time.monotonic()
    span = max(end - t0, 1e-3)
    T0, T1 = 0.8, 0.05
    while cost > 0:
        now = time.monotonic()
        if now >= end:
            break
        T = T0 * (T1 / T0) ** ((now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in S or (a2, b1) in S:
            continue
        # Forward swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
        adj[a1].discard(b1)
        adj[b1].discard(a1)
        adj[a2].discard(b2)
        adj[b2].discard(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)
        c2 = _ball_cost(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add((a1, b2))
            S.add((a2, b1))
            E[i] = [a1, b2]
            E[j] = [a2, b1]
            cost = c2
        else:
            # Revert the swap.
            adj[a1].discard(b2)
            adj[b2].discard(a1)
            adj[a2].discard(b1)
            adj[b1].discard(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)
    if cost == 0:
        return [tuple(e) for e in E]
    return None


def _search(start_n, start_edges, d, D, deadline, rng, consider):
    """Repeatedly grow the current graph by two vertices and repair it."""
    E = _orient(start_n, start_edges)
    if E is None:
        return
    cur_n, cur_E = start_n, E
    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline:
        if cur_n + 2 > moore:
            break
        aug = _augment(cur_n, cur_E, d, rng)
        if aug is None:
            break
        n2, E2 = aug
        att_end = min(deadline, time.monotonic() + ATT)
        res = _anneal(n2, E2, D, rng, att_end)
        if res is None:
            continue
        edges = [(a, b) for a, b in res]
        if lib.is_valid(n2, edges, d, D):
            consider(n2, edges)
            cur_n, cur_E = n2, res


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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    if D >= 3:
        # Record-level and standard diameter-3 base graphs.
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Bold path: grow the best base and repair it by annealing.
        _search(best[0], best[1], d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
