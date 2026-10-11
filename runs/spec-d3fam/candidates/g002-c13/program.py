import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold family for diameter-3 targets: simulated annealing over bipartite graphs
# with vertex insertion and edge freeing. Starts from a strong algebraic base,
# keeps every intermediate state bipartite and within the degree bound, and
# records a state only when all pairs are within distance D.
# ----------------------------------------------------------------------------

def _ball_bits(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bad(n, adj, D):
    """Number of unordered pairs at distance greater than D."""
    return sum(n - x.bit_count() for x in _ball_bits(n, adj, D)) // 2


def _bipartition(n, adj):
    """Two-colouring of a bipartite adjacency structure."""
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


def _to_edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _anneal_grow(n, edges, d, D, deadline, rng):
    """Annealed vertex insertion. Returns the best valid (n, edges) found, or None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    cur = _bad(n, adj, D)
    best = (n, list(edges)) if cur == 0 else None
    best_n = n if cur == 0 else 0
    cap = int(n * 1.12) + 2
    T = 0.6

    while time.monotonic() < deadline:
        c = rng.randrange(2)
        opp = [u for u in range(n) if color[u] == 1 - c]
        spare = [u for u in opp if len(adj[u]) < d]
        full = [u for u in opp if len(adj[u]) >= d]
        rng.shuffle(spare)
        chosen = spare[:d]
        removed = []
        need = d - len(chosen)
        if need > 0 and full and n + 1 <= cap:
            rng.shuffle(full)
            for u in full[:need]:
                w = rng.choice(adj[u])
                removed.append((u, w))
                chosen.append(u)
        if len(chosen) < 2 or n + 1 > cap:
            T = max(0.15, T * 0.9995)
            continue

        # Apply the move.
        for u, w in removed:
            adj[u].remove(w)
            adj[w].remove(u)
        v = n
        adj.append([])
        color.append(c)
        for u in chosen:
            adj[u].append(v)
            adj[v].append(u)
        n2 = n + 1

        new = _bad(n2, adj, D)
        delta = new - cur
        T = max(0.15, T * 0.9995)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            n = n2
            cur = new
            if cur == 0 and n > best_n:
                best = (n, _to_edges(n, adj))
                best_n = n
        else:
            # Undo: detach v, drop its vertex, restore removed edges.
            for u in chosen:
                adj[u].remove(v)
            adj.pop()
            color.pop()
            for u, w in removed:
                adj[u].append(w)
                adj[w].append(u)
    return best


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _largest_pg_below(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        # Moore-optimal case.
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Known record base for d-2 a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass
        # Plain projective plane base.
        pg = _largest_pg_below(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Bold search: annealed insertion from the strongest base available.
        base = best
        if base[0] >= 4:
            res = _anneal_grow(base[0], base[1], d, D, deadline, rng)
            if res is not None:
                consider(res[0], res[1])

    if D >= 2 and not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
