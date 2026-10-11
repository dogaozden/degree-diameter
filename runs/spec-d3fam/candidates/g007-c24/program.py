import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _pg(d):
    """Point-line incidence graph of PG(2, q), q the largest prime power with q + 1 <= d."""
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
# Graph helpers on adjacency lists.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of adjacency lists, or None if the graph is not bipartite."""
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
    return color


def _to_adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _to_edges(n, adj):
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance greater than D (bitmask balls)."""
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


def _set_edge(adj, S, E, i, new):
    """Replace the edge E[i] by `new` (both stored as (side-0 vertex, side-1 vertex)) in all structures."""
    a, b = E[i]
    adj[a].remove(b)
    adj[b].remove(a)
    S.discard((a, b))
    x, y = new
    adj[x].append(y)
    adj[y].append(x)
    S.add(new)
    E[i] = new


# ----------------------------------------------------------------------------
# New construction: pair insertion by edge rerouting, then annealing repair.
#
# Insert two new vertices v (side 0) and w (side 1) joined to each other. Pick a
# matching M of d-1 existing edges (t_i, x_i) with t_i on side 1 and x_i on side 0.
# Reroute each edge: v takes t_i and w takes x_i. Every old vertex keeps its degree,
# and v, w end with degree d. The distances are generally broken, so run a
# simulated-annealing repair over degree-preserving double-edge swaps until the
# number of pairs at distance > D is zero.
# ----------------------------------------------------------------------------

def _attempt_insert(n, color, adj, E, d, D, rng, deadline, iters):
    """Try to add two vertices with repair. Returns (n+2, adj, color, E) on success, else None."""
    adj = [list(a) for a in adj] + [[], []]
    color = list(color) + [0, 1]
    v, w = n, n + 1
    E = list(E)
    S = set(E)

    # Random matching of d-1 edges with pairwise distinct endpoints.
    order = list(range(len(E)))
    rng.shuffle(order)
    used_a, used_b, M = set(), set(), []
    for i in order:
        a, b = E[i]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        M.append(i)
        if len(M) == d - 1:
            break
    if len(M) < d - 1:
        return None

    for i in M:
        a, b = E[i]
        # Replace (a, b) by (v, b); add (a, w).
        _set_edge(adj, S, E, i, (v, b))
        adj[a].append(w)
        adj[w].append(a)
        S.add((a, w))
        E.append((a, w))
    adj[v].append(w)
    adj[w].append(v)
    S.add((v, w))
    E.append((v, w))

    nn = n + 2
    cost = _bad(nn, adj, D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            return None
        T = max(0.15, 1.5 * (1.0 - it / max(1, iters)))
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        old1, old2 = E[i], E[j]
        _set_edge(adj, S, E, i, (a1, b2))
        _set_edge(adj, S, E, j, (a2, b1))
        nc = _bad(nn, adj, D)
        delta = nc - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = nc
        else:
            _set_edge(adj, S, E, i, old1)
            _set_edge(adj, S, E, j, old2)

    if cost == 0:
        return nn, adj, color, E
    return None


def _grow(n, adj, color, E, d, D, deadline, rng):
    """Repeatedly insert vertex pairs with repair. Returns the largest state reached."""
    best = (n, adj, color, E)
    fails = 0
    while time.monotonic() < deadline:
        cn, cadj, ccolor, cE = best
        res = _attempt_insert(cn, ccolor, cadj, cE, d, D, rng, deadline, 1500)
        if res is None:
            fails += 1
            if fails > 400:
                break
            continue
        fails = 0
        best = res
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D == 2:
        return best

    starts = []
    for cand in (_araujo(d), _pg(d)):
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            starts.append(cand)
    starts.sort(key=lambda c: -c[0])
    for c in starts:
        consider(c[0], c[1])

    # Grow each start with the pair-insertion repair, sharing the remaining time.
    for idx, c in enumerate(starts):
        now = time.monotonic()
        if now >= deadline:
            break
        sub_deadline = now + (deadline - now) / (len(starts) - idx)
        n0, e0 = c
        adj = _to_adj(n0, e0)
        color = _bipartition(n0, adj)
        if color is None:
            continue
        E = [(a, b) for a in range(n0) if color[a] == 0 for b in adj[a]]
        n1, adj1, _, _ = _grow(n0, adj, color, E, d, D, sub_deadline, rng)
        if n1 > n0:
            consider(n1, _to_edges(n1, adj1))

    # Ensure the returned graph is valid.
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
