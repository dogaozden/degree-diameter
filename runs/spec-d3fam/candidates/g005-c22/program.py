import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (safe fallbacks).
# ----------------------------------------------------------------------------

def _ara(d):
    """Araujo-Pardo & Lopez graph for d = q + 2, q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            try:
                return lib.projective_plane_incidence(q)
            except Exception:
                return None
    return None


# ----------------------------------------------------------------------------
# Unstructured search: penalised annealing over bipartite edge sets.
# The state is a bipartite graph on n vertices (sides 0 and 1). Moves rewire an
# edge or add one. Cost = (# unordered pairs at distance > D) + 3 * (degree excess).
# Whenever the cost reaches 0 the graph is recorded and grown by one vertex per side.
# ----------------------------------------------------------------------------

def _sides(n, adj):
    """Two-colouring of a graph given by adjacency sets (isolated vertices get colour 0)."""
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


def _cost(n, adj, D, d):
    """Penalised cost of the current graph; zero iff it is a valid degree-d, diameter-D graph."""
    B = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = B[v]
            for u in adj[v]:
                x |= B[u]
            nb.append(x)
        B = nb
    bad = 0
    for x in B:
        bad += n - x.bit_count()
    bad //= 2
    exc = 0
    for v in range(n):
        k = len(adj[v]) - d
        if k > 0:
            exc += k
    return bad + 3 * exc


def _remove_at(E, ES, adj, idx):
    a, b = E[idx]
    E[idx] = E[-1]
    E.pop()
    ES.discard((a, b))
    adj[a].discard(b)
    adj[b].discard(a)


def _add(E, ES, adj, a, b):
    E.append((a, b))
    ES.add((a, b))
    adj[a].add(b)
    adj[b].add(a)


def _remove(E, ES, adj, a, b):
    _remove_at(E, ES, adj, E.index((a, b)))


def _search(n0, adj0, side0, d, D, deadline, rng):
    """Anneal from a valid start graph; returns the largest valid graph found as (n, edges), or None."""
    n = n0
    adj = [set(s) for s in adj0]
    side = list(side0)
    E, ES = [], set()
    for u in range(n):
        if side[u] == 0:
            for v in adj[u]:
                E.append((u, v))
                ES.add((u, v))
    L0 = [v for v in range(n) if side[v] == 0]
    L1 = [v for v in range(n) if side[v] == 1]

    cur = _cost(n, adj, D, d)
    best = None
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 0.6, 0.05

    while time.monotonic() < deadline:
        if cur == 0:
            # Valid graph: record it, then grow by one isolated vertex per side.
            best = (n, list(E))
            x, y = n, n + 1
            n += 2
            adj.append(set())
            adj.append(set())
            side.append(0)
            side.append(1)
            L0.append(x)
            L1.append(y)
            cur = _cost(n, adj, D, d)
            continue

        frac = min(1.0, (time.monotonic() - t0) / span)
        T = T0 * (T1 / T0) ** frac

        if E and rng.random() < 0.8:
            # Rewire: move edge (a, b) to a random non-edge (a2, b2).
            idx = rng.randrange(len(E))
            a, b = E[idx]
            a2 = rng.choice(L0)
            b2 = rng.choice(L1)
            if (a2, b2) in ES:
                continue
            _remove_at(E, ES, adj, idx)
            _add(E, ES, adj, a2, b2)
            new = _cost(n, adj, D, d)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                _remove(E, ES, adj, a2, b2)
                _add(E, ES, adj, a, b)
        else:
            # Add a non-edge between two vertices that still have spare degree.
            a2 = rng.choice(L0)
            b2 = rng.choice(L1)
            if (a2, b2) in ES or len(adj[a2]) >= d or len(adj[b2]) >= d:
                continue
            _add(E, ES, adj, a2, b2)
            new = _cost(n, adj, D, d)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                _remove(E, ES, adj, a2, b2)

    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    # Algebraic starting points for D >= 3, each checked before use.
    if D >= 3:
        for cand in (_ara(d), _pg(d)):
            if cand is not None and cand[0] > best_n and lib.is_valid(cand[0], cand[1], d, D):
                best, best_n = cand, cand[0]

    # Unstructured annealing, started from the best valid graph found so far.
    n0, e0 = best
    adj0 = [set() for _ in range(n0)]
    for u, v in e0:
        adj0[u].add(v)
        adj0[v].add(u)
    side0 = _sides(n0, adj0)
    res = _search(n0, adj0, side0, d, D, deadline, rng)
    if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
        best = res

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
