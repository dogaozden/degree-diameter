import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Seeds: K_{d,d}, projective-plane incidence graphs, and Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _kdd(d):
    """K_{d,d}: valid for every D >= 2."""
    return 2 * d, [(a, d + b) for a in range(d) for b in range(d)]


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            try:
                return lib.projective_plane_incidence(q)
            except Exception:
                return None
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _orient(n, edges):
    """Orient each edge as (left, right) using a BFS two-colouring of a bipartite graph."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s0 in range(n):
        if col[s0] != -1:
            continue
        col[s0] = 0
        stack = [s0]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return [(u, v) if col[u] == 0 else (v, u) for u, v in edges]


# ----------------------------------------------------------------------------
# Mutable state: an oriented edge list [left, right] plus adjacency sets.
# ----------------------------------------------------------------------------

class _State:
    def __init__(self, n, E):
        self.n = n
        self.E = [list(e) for e in E]
        self.adj = [set() for _ in range(n)]
        for a, b in self.E:
            self.adj[a].add(b)
            self.adj[b].add(a)


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _cost(s, D):
    """Number of ordered vertex pairs at distance > D (unreachable pairs included). Zero means valid."""
    balls = _balls(s.n, s.adj, D)
    return sum(s.n - b.bit_count() for b in balls)


def _insert(s, d, rng):
    """Add a new left vertex x and a new right vertex y, both of degree d.

    Pick d disjoint edges (a_i, b_i). Each a_i swaps its neighbour b_i for y, and
    each b_i swaps its neighbour a_i for x. All old degrees are preserved.
    """
    order = list(range(len(s.E)))
    rng.shuffle(order)
    ua, ub, chosen = set(), set(), []
    for i in order:
        a, b = s.E[i]
        if a in ua or b in ub:
            continue
        ua.add(a)
        ub.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return False
    x, y = s.n, s.n + 1
    s.n += 2
    s.adj.append(set())
    s.adj.append(set())
    chs = set(chosen)
    rem = [s.E[i] for i in chosen]
    s.E = [e for k, e in enumerate(s.E) if k not in chs]
    for a, b in rem:
        s.adj[a].discard(b)
        s.adj[b].discard(a)
    for a, b in rem:
        s.E.append([a, y])
        s.adj[a].add(y)
        s.adj[y].add(a)
        s.E.append([x, b])
        s.adj[x].add(b)
        s.adj[b].add(x)
    return True


def _anneal(s, D, deadline, rng):
    """Degree-preserving 2-switch annealing that drives the bad-pair count to zero."""
    cur = _cost(s, D)
    T = 1.0
    while cur > 0 and time.monotonic() < deadline:
        m = len(s.E)
        if m < 2:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = s.E[i]
        c, e = s.E[j]
        if a == c or b == e or e in s.adj[a] or b in s.adj[c]:
            continue
        # Apply (a,b),(c,e) -> (a,e),(c,b).
        s.adj[a].discard(b)
        s.adj[b].discard(a)
        s.adj[c].discard(e)
        s.adj[e].discard(c)
        s.adj[a].add(e)
        s.adj[e].add(a)
        s.adj[c].add(b)
        s.adj[b].add(c)
        new = _cost(s, D)
        T = max(0.2, T * 0.999)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            s.E[i] = [a, e]
            s.E[j] = [c, b]
        else:
            # Revert.
            s.adj[a].discard(e)
            s.adj[e].discard(a)
            s.adj[c].discard(b)
            s.adj[b].discard(c)
            s.adj[a].add(b)
            s.adj[b].add(a)
            s.adj[c].add(e)
            s.adj[e].add(c)
    return cur == 0


def _grow(seed_n, seed_E, d, D, deadline, rng, consider):
    """Repeatedly insert a vertex pair and repair diameter by 2-switch annealing.

    Each success becomes the new snapshot. A failed repair restores the snapshot.
    """
    cur_n, cur_E = seed_n, seed_E
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        s = _State(cur_n, cur_E)
        if not _insert(s, d, rng):
            break
        rem = deadline - time.monotonic()
        budget = min(rem, max(0.5, rem * 0.05))
        if _anneal(s, D, time.monotonic() + budget, rng):
            cur_n = s.n
            cur_E = [(a, b) for a, b in s.E]
            consider(cur_n, cur_E)
            fails = 0
        else:
            fails += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback, valid for D >= 2.
    best = _kdd(d)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])

    # Growth-and-repair from the best valid seed. The seed is oriented
    # left-to-right so that the switch moves are well defined.
    rng = random.Random(seed * 1000003 + d * 101 + D)
    seed_n, seed_edges = best
    seed_E = _orient(seed_n, seed_edges)
    _grow(seed_n, seed_E, d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best
