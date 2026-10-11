import math
import random
import time
import itertools

import lib


# ----------------------------------------------------------------------------
# Small graph utilities (set-based adjacency, bipartition, saturation).
# ----------------------------------------------------------------------------

def _adjsets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
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


def _orient(n, edges):
    """Return edges as (A, B) pairs where A is colour 0 and B is colour 1."""
    color = _bipartition(n, _adjsets(n, edges))
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


def _saturate(n, edges, d, rng):
    """Add edges between deficient opposite-colour vertices. Never hurts diameter or bipartiteness."""
    adj = _adjsets(n, edges)
    color = _bipartition(n, adj)
    E = list(edges)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].add(b)
            adj[b].add(a)
            E.append((a, b))
    return E


# ----------------------------------------------------------------------------
# Fast bad-pair count via bitsets over a mutable adjacency.
# ----------------------------------------------------------------------------

def _ball_bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset ball expansion)."""
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


def _toggle(adj, u, v, on):
    if on:
        adj[u].add(v)
        adj[v].add(u)
    else:
        adj[u].discard(v)
        adj[v].discard(u)


# ----------------------------------------------------------------------------
# NEW: matching-insertion with degree-preserving switch annealing.
#
# Insert one new A-vertex a and one new B-vertex b. Pick d vertex-disjoint
# edges (x_i, y_i) of the current graph. Replace each by (x_i, b) and add
# (a, y_i). Every old vertex keeps its degree, a and b get degree d. Then
# anneal over double-edge switches (x1,y1),(x2,y2) -> (x1,y2),(x2,y1), which
# preserve all degrees and bipartiteness, minimising the number of pairs at
# distance > D. A zero-cost state is a larger valid graph.
# ----------------------------------------------------------------------------

def _switch_anneal(n, E0, d, D, attempt_end, rng):
    adj = [set() for _ in range(n + 2)]
    for x, y in E0:
        adj[x].add(y)
        adj[y].add(x)
    a, b = n, n + 1  # a on side A (colour 0), b on side B (colour 1)

    idx = list(range(len(E0)))
    rng.shuffle(idx)
    used = set()
    chosen = []
    for i in idx:
        x, y = E0[i]
        if x in used or y in used:
            continue
        used.add(x)
        used.add(y)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        raise ValueError("not enough disjoint edges")

    E = [list(e) for e in E0]
    for i in chosen:
        x, y = E[i]
        _toggle(adj, x, y, False)
        E[i] = [x, b]
        _toggle(adj, x, b, True)
        E.append([a, y])
        _toggle(adj, a, y, True)

    N = n + 2
    M = len(E)
    cost = _ball_bad(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-6, attempt_end - t0)
    T0, T1 = 2.0, 0.15
    while cost > 0:
        now = time.monotonic()
        if now >= attempt_end:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        x1, y1 = E[i]
        x2, y2 = E[j]
        if x1 == x2 or y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
            continue
        _toggle(adj, x1, y1, False)
        _toggle(adj, x2, y2, False)
        _toggle(adj, x1, y2, True)
        _toggle(adj, x2, y1, True)
        c2 = _ball_bad(N, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            E[i] = [x1, y2]
            E[j] = [x2, y1]
        else:
            _toggle(adj, x1, y2, False)
            _toggle(adj, x2, y1, False)
            _toggle(adj, x1, y1, True)
            _toggle(adj, x2, y2, True)

    if cost != 0:
        return None
    return N, [(x, y) for x, y in E]


def _grow(n, E, d, D, deadline, rng):
    """Repeatedly insert a vertex pair by switch annealing, keeping only valid states."""
    cur_n, cur = n, E
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        attempt_end = min(deadline, now + max(3.0, remaining / 2))
        try:
            res = _switch_anneal(cur_n, cur, d, D, attempt_end, rng)
        except ValueError:
            break
        if res is None:
            continue
        n2, e2 = res
        if not lib.is_valid(n2, e2, d, D):
            break
        cur_n, cur = n2, e2
    return cur_n, cur


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and max degree d.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        # Moore-optimal: PG(2, d-1) incidence graph.
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Candidate bases.
    bases = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))
        except (ValueError, StopIteration, KeyError):
            pass
    pg = _best_pg(d)
    if pg is not None:
        bases.append(pg)

    valid_bases = []
    for n0, e0 in bases:
        if lib.is_valid(n0, e0, d, D):
            valid_bases.append((n0, e0))
            consider(n0, e0)
    if not valid_bases:
        return best

    n0, e0 = max(valid_bases, key=lambda t: t[0])

    # Use spare degree, then grow by matching insertion + switch annealing.
    E = _saturate(n0, e0, d, rng)
    E = _orient(n0, E)
    consider(n0, E)

    cur_n, cur = _grow(n0, E, d, D, deadline, rng)
    consider(cur_n, cur)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
