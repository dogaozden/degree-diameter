import math
import random
import time

import lib

# Construction notes:
#  - D = 2 and D = 3 bases: K_{d,d}, PG(2,q) incidence, and the Araujo-Pardo-Lopez graph.
#  - New routine (D = 3): a grow-and-repair annealer. It starts from the best base graph,
#    adds a vertex of one colour joined to d opposite-colour vertices (stealing slots from
#    their existing edges), then repairs the diameter by annealing over edge insertions.
#    Each insertion evicts a random edge at any saturated endpoint. The cost is the number
#    of vertex pairs at distance > 3, so cost 0 means a valid graph. Each zero-cost state
#    is validated with lib.is_valid and kept if it is the largest so far.
#  - Other diameters keep the simple K_{d,d} fallback, since only the D = 3 targets are scored here.


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
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


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given as adjacency sets."""
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


def _cost(n, adj):
    """Return (number of unordered pairs at distance > 3, per-vertex radius-3 balls as bitmasks)."""
    ball = [1 << v for v in range(n)]
    for _ in range(3):
        nxt = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return sum(n - b.bit_count() for b in ball) // 2, ball


def _search(n, edges, d, deadline, rng, consider):
    """Grow-and-repair annealing for diameter 3. Calls consider(n, E) on each zero-cost state."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, adj)
    omask = [0, 0]
    for v in range(n):
        omask[color[v]] |= 1 << v
    cur, ball = _cost(n, adj)
    T = 0.6

    while time.monotonic() < deadline:
        if cur == 0:
            E = [(u, v) for u in range(n) for v in adj[u] if u < v]
            consider(n, E)
            # Grow: add a vertex of colour c adjacent to d opposite-colour vertices.
            c = rng.randrange(2)
            v = n
            n += 1
            adj.append(set())
            color.append(c)
            omask[c] |= 1 << v
            opp = [x for x in range(v) if color[x] != c]
            for x in rng.sample(opp, d):
                if len(adj[x]) >= d:
                    y = rng.choice(list(adj[x]))
                    adj[x].discard(y)
                    adj[y].discard(x)
                adj[x].add(v)
                adj[v].add(x)
            cur, ball = _cost(n, adj)
            T = 0.6
            continue

        # Move: pick a vertex u and an opposite-colour w at distance > 3, then join them.
        u = rng.randrange(n)
        miss = omask[1 - color[u]] & ~ball[u]
        if miss == 0:
            continue
        k = rng.randrange(miss.bit_count())
        for _ in range(k):
            miss &= miss - 1
        w = (miss & -miss).bit_length() - 1

        removed = []
        for x in (u, w):
            if len(adj[x]) >= d:
                y = rng.choice(list(adj[x]))
                adj[x].discard(y)
                adj[y].discard(x)
                removed.append((x, y))
        adj[u].add(w)
        adj[w].add(u)

        new, nb = _cost(n, adj)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur, ball = new, nb
        else:
            adj[u].discard(w)
            adj[w].discard(u)
            for x, y in removed:
                adj[x].add(y)
                adj[y].add(x)
        T = max(0.05, T * 0.9995)


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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        for g in (_ara(d), _best_pg(d)):
            if g is not None:
                consider(g[0], g[1])

    if D == 3 and d >= 3:
        _search(best[0], best[1], d, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
