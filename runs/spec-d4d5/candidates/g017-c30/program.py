import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: simulated annealing over d-regular bipartite graphs.
#
# The search keeps a d-regular bipartite graph and minimises the number of
# vertex pairs at distance > D. Moves are degree-preserving 2-switches, which
# keep the graph bipartite. When the cost reaches zero, the graph is recorded
# and grown by a degree-preserving vertex insertion, then annealed again.
# Starting points: the projective plane incidence graph when d-1 is a prime
# power, otherwise a circulant Haar graph. The fallback is K_{d,d}.
# ----------------------------------------------------------------------------


def _bad(adj, n, D):
    """Number of unordered pairs at distance > D (bitmask BFS)."""
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


class _G:
    """Mutable bipartite graph: side 0 = A, side 1 = B; E holds (A, B) pairs."""

    def __init__(self, n, adj, E, side):
        self.n = n
        self.adj = adj
        self.E = E
        self.side = side
        self.eset = set(E)


def _replace(lst, old, new):
    lst[lst.index(old)] = new


def _swap(g, i, j):
    """2-switch on edges i and j: (x1,y1),(x2,y2) -> (x1,y2),(x2,y1). Involution."""
    adj, E, eset = g.adj, g.E, g.eset
    x1, y1 = E[i]
    x2, y2 = E[j]
    _replace(adj[x1], y1, y2)
    _replace(adj[y2], x2, x1)
    _replace(adj[x2], y2, y1)
    _replace(adj[y1], x1, x2)
    eset.discard((x1, y1))
    eset.discard((x2, y2))
    eset.add((x1, y2))
    eset.add((x2, y1))
    E[i] = (x1, y2)
    E[j] = (x2, y1)


def _valid_swap(g, i, j):
    x1, y1 = g.E[i]
    x2, y2 = g.E[j]
    return (x1 != x2 and y1 != y2
            and (x1, y2) not in g.eset and (x2, y1) not in g.eset)


def _anneal(g, d, D, rng, deadline, iters):
    """Metropolis search on 2-switches. Returns the final cost (0 means valid)."""
    cost = _bad(g.adj, g.n, D)
    if cost == 0 or len(g.E) < 2:
        return cost
    T0, T1 = 2.0, 0.2
    for it in range(iters):
        if cost == 0:
            break
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i, j = rng.sample(range(len(g.E)), 2)
        if not _valid_swap(g, i, j):
            continue
        _swap(g, i, j)
        c2 = _bad(g.adj, g.n, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _swap(g, i, j)
    return cost


def _grow(g, d, rng):
    """Degree-preserving insertion of one A vertex and one B vertex (adds 2 vertices)."""
    idx = None
    for _ in range(500):
        cand = rng.sample(range(len(g.E)), d)
        As = {g.E[t][0] for t in cand}
        Bs = {g.E[t][1] for t in cand}
        if len(As) == d and len(Bs) == d:
            idx = cand
            break
    if idx is None:
        return False
    na = g.n
    nb = g.n + 1
    g.adj.append([])
    g.adj.append([])
    g.side.append(0)
    g.side.append(1)
    g.n += 2
    chosen = set(idx)
    keep = [g.E[t] for t in range(len(g.E)) if t not in chosen]
    new = []
    for t in idx:
        a, b = g.E[t]
        g.adj[a].remove(b)
        g.adj[b].remove(a)
        g.eset.discard((a, b))
        g.adj[a].append(nb)
        g.adj[nb].append(a)
        g.adj[b].append(na)
        g.adj[na].append(b)
        g.eset.add((a, nb))
        g.eset.add((na, b))
        new.append((a, nb))
        new.append((na, b))
    g.E = keep + new
    return True


def _pg_state(d):
    """d-regular incidence graph of PG(2, d-1) when d-1 is a prime power."""
    q = d - 1
    if q < 2 or not lib.is_prime_power(q):
        return None
    n, edges = lib.projective_plane_incidence(q)
    m = n // 2
    adj = [[] for _ in range(n)]
    E = []
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        E.append((u, v))
    side = [0] * m + [1] * m
    return _G(n, adj, E, side)


def _haar_state(d):
    """Circulant d-regular bipartite graph on k = d plus d vertices per side (K_{d,d})."""
    k = d
    adj = [[] for _ in range(2 * k)]
    E = []
    for i in range(k):
        for s in range(d):
            b = k + (i + s) % k
            adj[i].append(b)
            adj[b].append(i)
            E.append((i, b))
    side = [0] * k + [1] * k
    return _G(2 * k, adj, E, side)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 3.0)
    deadline = start + max(0.0, budget)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    if D <= 2 or time.monotonic() >= deadline:
        return best if lib.is_valid(best[0], best[1], d, D) else lib.haar_graph(d, range(d))

    g = _pg_state(d)
    if g is None:
        g = _haar_state(d)

    # Record the starting graph if it is valid and larger.
    if g.n > best_n:
        e0 = list(g.E)
        if lib.is_valid(g.n, e0, d, D):
            best = (g.n, e0)
            best_n = g.n

    while time.monotonic() < deadline:
        c = _anneal(g, d, D, rng, deadline, iters=4000)
        if c == 0:
            n = g.n
            edges = list(g.E)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
            if time.monotonic() >= deadline:
                break
            if not _grow(g, d, rng):
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
