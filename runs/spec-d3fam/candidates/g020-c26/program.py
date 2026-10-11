import math
import random
import time

import lib

# Experimental search: start from the best known diameter-3 base (projective plane
# or Araujo-Pardo-Lopez graph), add pairs of vertices, and anneal the edge set to
# remove all pairs at distance > D. The safe base is always kept, so every returned
# graph has been checked with lib.is_valid.

_STAGE = 3000  # annealing iterations per temperature cycle


def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _al_base(d):
    """Araujo-Pardo & Lopez graph for q = d - 2 a prime power (degree d, diameter 3)."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, StopIteration, KeyError):
        return None


def _two_color(n, adj):
    """Bipartition of the graph given by adjacency sets, or None if not bipartite."""
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


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D."""
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


def _apply(adj, deg, edits):
    for op, u, v in edits:
        if op == '+':
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
        else:
            adj[u].discard(v)
            adj[v].discard(u)
            deg[u] -= 1
            deg[v] -= 1


def _undo(adj, deg, edits):
    _apply(adj, deg, [('-' if op == '+' else '+', u, v) for op, u, v in reversed(edits)])


def _fill(n, adj, deg, color, d, rng, tries):
    """Greedily add edges between deficient opposite-side vertices. Never hurts distances."""
    A = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    B = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    if not A or not B:
        return 0
    added = 0
    for _ in range(tries):
        a = rng.choice(A)
        b = rng.choice(B)
        if deg[a] < d and deg[b] < d and b not in adj[a]:
            _apply(adj, deg, [('+', a, b)])
            added += 1
    return added


def _propose(n, adj, deg, color, d, rng):
    """Random degree-respecting move: a rewire into a deficient vertex, or a 2-switch."""
    a = None
    for _ in range(30):
        x = rng.randrange(n)
        if adj[x]:
            a = x
            break
    if a is None:
        return None
    b = rng.choice(tuple(adj[a]))
    if rng.random() < 0.4:
        # Replace edge (a, b) by (a, y), y deficient on b's side.
        defs = [y for y in range(n)
                if y != b and color[y] == color[b] and deg[y] < d and y not in adj[a]]
        if not defs:
            return None
        y = rng.choice(defs)
        return [('-', a, b), ('+', a, y)]
    # 2-switch: (a, b), (c, e) -> (a, e), (c, b). Preserves all degrees.
    c = None
    for _ in range(30):
        x = rng.randrange(n)
        if x != a and color[x] == color[a] and adj[x]:
            c = x
            break
    if c is None:
        return None
    e = rng.choice(tuple(adj[c]))
    if e == b or e in adj[a] or b in adj[c]:
        return None
    return [('-', a, b), ('-', c, e), ('+', a, e), ('+', c, b)]


def _edges(n, adj, color):
    return [(v, u) for v in range(n) if color[v] == 0 for u in adj[v]]


def _search(n0, edges0, d, D, rng, deadline):
    """Grow by vertex pairs, annealing the edge set to reach diameter <= D after each pair."""
    n = n0
    adj = [set() for _ in range(n)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n, adj)
    if color is None:
        return None
    deg = [len(s) for s in adj]
    best = (n0, list(edges0))
    cur = _bad(n, adj, D)
    it = 0
    while time.monotonic() < deadline:
        if _fill(n, adj, deg, color, d, rng, 50):
            cur = _bad(n, adj, D)
        if cur == 0:
            edges = _edges(n, adj, color)
            if not lib.is_valid(n, edges, d, D):
                break
            best = (n, edges)
            # Success: add one more vertex on each side.
            adj.append(set())
            adj.append(set())
            deg.extend([0, 0])
            color.extend([0, 1])
            n += 2
            cur = _bad(n, adj, D)
            it = 0
            continue
        it += 1
        frac = (it % _STAGE) / _STAGE
        T = 3.0 * (0.05 / 3.0) ** frac
        edits = _propose(n, adj, deg, color, d, rng)
        if edits is None:
            continue
        _apply(adj, deg, edits)
        new = _bad(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _undo(adj, deg, edits)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    cands = []
    pg = _pg_base(d)
    if pg is not None:
        cands.append(pg)
    al = _al_base(d)
    if al is not None:
        cands.append(al)
    for n_c, e_c in cands:
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)

    # Moore bound for D = 3 is 2(d^2 - d + 1); the PG(2, d-1) case already meets it.
    if D == 3 and best[0] < 2 * (d * d - d + 1) and time.monotonic() < deadline:
        res = _search(best[0], best[1], d, D, rng, deadline)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
