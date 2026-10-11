import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Graph helpers on mutable adjacency sets.
# ----------------------------------------------------------------------------

def _apply(adj, ops):
    """Apply a list of (sign, u, v) ops: sign 1 adds edge uv, sign 0 removes it."""
    for s, u, v in ops:
        if s:
            adj[u].add(v)
            adj[v].add(u)
        else:
            adj[u].discard(v)
            adj[v].discard(u)


def _undo(adj, ops):
    """Reverse a list of ops applied by _apply."""
    _apply(adj, [(1 - s, u, v) for s, u, v in reversed(ops)])


def _colors(n, adj):
    """Two-colouring of a bipartite graph given by adjacency sets."""
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
    """Number of unordered pairs at distance > D (unreachable counts). Zero means diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# NEW: degree-preserving local search that inserts a vertex pair.
#
# Given a bipartite graph with max degree d and diameter <= D, append one new
# A-vertex x and one new B-vertex y, and anneal over graph states that keep
# every degree <= d and every edge joining the two colour classes. Two move
# types are used:
#   * 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Degrees are unchanged.
#   * add-with-eviction: add an edge (u,v) across the classes, first removing a
#     random edge at any endpoint that is already full. This lets x and y fill
#     up while evicting edges elsewhere.
# The cost is the number of pairs farther apart than D. Success means cost 0,
# which yields a valid graph with two more vertices.
# ----------------------------------------------------------------------------

def _two_switch(adj, L0, rng):
    a1 = rng.choice(L0)
    if not adj[a1]:
        return None
    b1 = rng.choice(list(adj[a1]))
    a2 = rng.choice(L0)
    if not adj[a2]:
        return None
    b2 = rng.choice(list(adj[a2]))
    if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
        return None
    ops = [(0, a1, b1), (0, a2, b2), (1, a1, b2), (1, a2, b1)]
    _apply(adj, ops)
    return ops


def _evict_add(adj, L0, L1, x, y, d, rng):
    pick = rng.random()
    if pick < 0.35:
        u, v = x, rng.choice(L1)
    elif pick < 0.7:
        u, v = rng.choice(L0), y
    else:
        u, v = rng.choice(L0), rng.choice(L1)
    if u == v or v in adj[u]:
        return None
    ops = []
    if len(adj[u]) >= d:
        w = rng.choice(list(adj[u]))
        ops.append((0, u, w))
        _apply(adj, [ops[-1]])
    if len(adj[v]) >= d:
        w = rng.choice(list(adj[v]))
        ops.append((0, v, w))
        _apply(adj, [ops[-1]])
    ops.append((1, u, v))
    _apply(adj, [ops[-1]])
    return ops


def _search_extend(n, adj, color, d, D, deadline, rng):
    """Anneal so that vertices n-2 (colour 0) and n-1 (colour 1) join a diameter-D graph. Returns True on success."""
    x, y = n - 2, n - 1
    L0 = [v for v in range(n) if color[v] == 0]
    L1 = [v for v in range(n) if color[v] == 1]

    # Greedy start: x attaches to deficient B-side vertices, y to deficient A-side vertices.
    cand = [v for v in L1 if v != y and len(adj[v]) < d]
    rng.shuffle(cand)
    for v in cand[:d]:
        _apply(adj, [(1, x, v)])
    cand = [v for v in L0 if v != x and len(adj[v]) < d]
    rng.shuffle(cand)
    for v in cand[:d]:
        _apply(adj, [(1, y, v)])

    cost = _bad(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, Tend = 3.0, 0.1
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        T = T0 * (Tend / T0) ** min(1.0, (now - t0) / span)
        if rng.random() < 0.3:
            ops = _two_switch(adj, L0, rng)
        else:
            ops = _evict_add(adj, L0, L1, x, y, d, rng)
        if ops is None:
            continue
        c2 = _bad(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _undo(adj, ops)
    return True


def _grow_pairs(n, edges, d, D, deadline, rng):
    """Repeatedly insert a vertex pair while the search succeeds before the deadline."""
    while time.monotonic() < deadline:
        adj = [set() for _ in range(n)]
        for u, v in edges:
            adj[u].add(v)
            adj[v].add(u)
        color = _colors(n, adj)
        adj.append(set())
        adj.append(set())
        color += [0, 1]
        if not _search_extend(n + 2, adj, color, d, D, deadline, rng):
            break
        n += 2
        edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, edges


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

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    bases = []
    # Projective plane incidence: Moore-optimal for D = 3 when d-1 is a prime power.
    if lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if D == 3 and lib.is_valid(n, e, d, D):
            return n, e
        bases.append((n, e))
    # Araujo-Pardo & Lopez record family for d-2 a prime power.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))
        except ValueError:
            pass
    # Largest projective plane incidence graph with degree q+1 <= d.
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            bases.append(lib.projective_plane_incidence(q))
            break

    bases.sort(key=lambda b: b[0], reverse=True)
    base = None
    for n, e in bases:
        if lib.is_valid(n, e, d, D):
            base = (n, e)
            break

    if base is not None and base[0] > best_n:
        best_n, best_e = base
        try:
            n2, e2 = _grow_pairs(best_n, best_e, d, D, deadline, rng)
            if n2 > best_n and lib.is_valid(n2, e2, d, D):
                best_n, best_e = n2, e2
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
