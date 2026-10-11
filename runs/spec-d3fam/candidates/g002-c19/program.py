import math
import random
import time

import lib

# Bold change: instead of only growing by cover extension, take the best
# algebraic base graph (projective plane or Araujo-Pardo-Lopez record) and
# repeatedly insert one new vertex, then repair the diameter with simulated
# annealing over degree-preserving 2-switches, attachment moves and fill moves.
# Every accepted state keeps bipartiteness and max degree <= d by construction.
# If an insertion cannot be repaired in its time slice, the state is rolled
# back, and the last verified graph is returned.


def _base(d):
    """Algebraic base graph for diameter 3 (or None)."""
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except ValueError:
            pass
    return None


def _color(n, adj):
    """Two-colouring of a bipartite graph given by adjacency sets."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad(n, adj, D):
    """Ordered count of vertex pairs at distance more than D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _add(adj, u, v, ops):
    adj[u].add(v)
    adj[v].add(u)
    ops.append((0, u, v))


def _rem(adj, u, v, ops):
    adj[u].discard(v)
    adj[v].discard(u)
    ops.append((1, u, v))


def _undo(adj, ops):
    for t, u, v in reversed(ops):
        if t == 0:
            adj[u].discard(v)
            adj[v].discard(u)
        else:
            adj[u].add(v)
            adj[v].add(u)


def _move(adj, col, n, d, w, rng, ops):
    """One random degree-safe, bipartite-safe move; records its changes in ops."""
    r = rng.random()
    if r < 0.4:
        # Attach the new vertex w to a random opposite-side x, evicting edges if needed.
        x = rng.randrange(n)
        if x == w or col[x] == col[w] or w in adj[x]:
            return
        if len(adj[x]) >= d:
            if not adj[x]:
                return
            _rem(adj, x, rng.choice(tuple(adj[x])), ops)
        if len(adj[w]) >= d:
            _rem(adj, w, rng.choice(tuple(adj[w])), ops)
        _add(adj, x, w, ops)
    elif r < 0.8:
        # 2-switch: (x1,y1),(x2,y2) -> (x1,y2),(x2,y1). Preserves all degrees.
        x1 = rng.randrange(n)
        if not adj[x1]:
            return
        y1 = rng.choice(tuple(adj[x1]))
        x2 = rng.randrange(n)
        if x2 == x1 or col[x2] != col[x1] or not adj[x2]:
            return
        y2 = rng.choice(tuple(adj[x2]))
        if y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
            return
        _rem(adj, x1, y1, ops)
        _rem(adj, x2, y2, ops)
        _add(adj, x1, y2, ops)
        _add(adj, x2, y1, ops)
    else:
        # Fill: join two deficient opposite-side vertices.
        x = rng.randrange(n)
        z = rng.randrange(n)
        if x == z or col[x] == col[z] or z in adj[x]:
            return
        if len(adj[x]) < d and len(adj[z]) < d:
            _add(adj, x, z, ops)


def _sa_insert(adj, col, d, D, rng, deadline):
    """Anneal until the graph (including the new last vertex) has diameter <= D."""
    n = len(adj)
    w = n - 1
    cost = _bad(n, adj, D)
    T = 4.0
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0 and time.monotonic() > deadline:
            return False
        T = max(0.3, T * 0.9995)
        ops = []
        _move(adj, col, n, d, w, rng, ops)
        if not ops:
            continue
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _undo(adj, ops)
    return True


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}-like Haar graph, diameter 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    if D >= 3:
        base = _base(d)
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            best = base
            n, e = base
            adj = [set() for _ in range(n)]
            for u, v in e:
                adj[u].add(v)
                adj[v].add(u)

            # Grow one vertex at a time, keeping every verified state.
            while time.monotonic() < deadline:
                n = len(adj)
                col = _color(n, adj)
                c = 0 if col.count(0) <= col.count(1) else 1
                now = time.monotonic()
                attempt_deadline = min(deadline, now + max(2.0, 0.5 * (deadline - now)))

                snap = [set(s) for s in adj]
                adj.append(set())
                col.append(c)
                ok = _sa_insert(adj, col, d, D, rng, attempt_deadline)
                if not ok:
                    adj[:] = snap
                    break

                m = len(adj)
                edges = [(u, v) for u in range(m) for v in adj[u] if u < v]
                if lib.is_valid(m, edges, d, D):
                    best = (m, edges)
                else:
                    adj[:] = snap
                    break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
