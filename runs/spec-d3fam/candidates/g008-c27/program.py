import math
import random
import time

import lib

TIME_FRAC = 0.85     # fraction of time_limit used before returning
MARGIN = 2.0         # seconds kept in reserve
ITER = 3000          # swap steps per growth attempt
MAX_FAILS = 6        # consecutive failed growth attempts before stopping


# ---------------------------------------------------------------- helpers

def _two_colour(n, adj):
    """Proper 2-colouring of a bipartite graph given as adjacency sets."""
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
    """Ordered count of vertex pairs at distance > D (bitmask BFS)."""
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


def _edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


# ---------------------------------------------------------------- growth move

def _grow(n, adj, col, d, D, rng, deadline):
    """Add two vertices P (colour 1) and L (colour 0), each of degree d.

    A random matching of d edges (a_i, b_i), a_i colour 0, b_i colour 1, is
    replaced by (a_i, P) and (b_i, L), so old degrees are unchanged. Then
    anneal with degree-preserving 2-switches that keep bipartiteness, minimising
    the number of pairs at distance > D. Returns (n+2, adj, col) or None.
    """
    adj = [set(s) for s in adj]
    col = list(col)

    oriented = [(u, v) for u in range(n) if col[u] == 0 for v in adj[u]]
    rng.shuffle(oriented)
    used, pick = set(), []
    for a, b in oriented:
        if a not in used and b not in used:
            pick.append((a, b))
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    P, L = n, n + 1
    N = n + 2
    adj.append(set())
    adj.append(set())
    col.append(1)
    col.append(0)
    for a, b in pick:
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)

    E = [(u, v) for u in range(N) if col[u] == 0 for v in adj[u]]
    M = len(E)
    cur = _bad(N, adj, D)
    for it in range(ITER):
        if cur == 0:
            break
        if time.monotonic() >= deadline:
            return None
        T = 1.5 * (1.0 - it / ITER) + 0.05
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # 2-switch: (a,b),(c,e) -> (a,e),(c,b); first entries are colour 0.
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    if cur != 0:
        return None
    return N, adj, col


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                       # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))

    # Structured starting point.
    base = None
    if D == 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            base = lib.projective_plane_incidence(d - 1)   # Moore-extremal
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                base = lib.araujo_lopez_graph(d - 2)        # record construction
            except Exception:
                base = None
    if base is None or not lib.is_valid(base[0], base[1], d, D):
        base = lib.haar_graph(d, range(d))                  # K_{d,d}: always valid
    n, edges = base
    best = (n, edges)

    # Growth: repeatedly add two vertices by annealing while time and Moore bound allow.
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _two_colour(n, adj)
    mb = lib._moore_bound(d, D)

    fails = 0
    while time.monotonic() < deadline and fails < MAX_FAILS and n + 2 <= mb:
        res = _grow(n, adj, col, d, D, rng, deadline)
        if res is None:
            fails += 1
            continue
        n2, adj2, col2 = res
        e2 = _edges(n2, adj2)
        if not lib.is_valid(n2, e2, d, D):
            fails += 1
            continue
        n, adj, col = n2, adj2, col2
        best = (n, e2)
        fails = 0

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base
