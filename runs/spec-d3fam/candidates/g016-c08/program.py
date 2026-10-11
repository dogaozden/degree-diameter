import math
import random
import time

import lib


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets."""
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


def _bad_count(n, adj, D):
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


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _augment(n, edges, d, D, rng, deadline, T0=1.0):
    """Add two vertices (point P, line L) via degree-preserving 2-switches annealed on bad-pair count.

    Each attempt uses a randomly chosen starting matching and a temperature T0,
    so repeated calls explore different regions of the space.
    Returns (n+2, edges) with diameter <= D, or None if the search fails before the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
    rng.shuffle(oriented)
    used, pick = set(), []
    for idx, (a, b) in enumerate(oriented):
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    picked = set(pick)
    E = [oriented[i] for i in range(len(oriented)) if i not in picked]
    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)
        E.append((a, P))
        E.append((L, b))

    M = len(E)
    cur = _bad_count(N, adj, D)
    T = T0
    steps = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        steps += 1
        if steps % 2000 == 0:
            T = max(0.05, T * 0.9)  # cool down over time
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return N, list(E)


def _candidate_bases(d, D):
    """Structured starting graphs for D = 3 (valid ones only)."""
    bases = []
    if D != 3:
        return bases
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            bases.append(lib.araujo_lopez_graph(q))   # order 2(q^2+q+5), degree d
        except ValueError:
            pass
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        bases.append(lib.projective_plane_incidence(q))  # order 2(q^2+q+1), degree d
    return [b for b in bases if lib.is_valid(b[0], b[1], d, D)]


def _fallback(d, D):
    """Always-valid small graph: K_{d,d} when diameter 2 suffices, else a single edge or a point."""
    if D >= 2 and d >= 1:
        n, edges = lib.haar_graph(d, range(d))
        if lib.is_valid(n, edges, d, D):
            return n, edges
    if d >= 1 and D >= 1:
        return 2, [(0, 1)]
    return 1, []


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    best = _fallback(d, D)
    bases = _candidate_bases(d, D)
    for b in bases:
        if b[0] > best[0]:
            best = b
    if not bases:
        return best

    mb = _moore(d, D)
    attempt = 0
    while time.monotonic() < deadline:
        attempt += 1
        # Multi-start: pick a base at random each attempt, then grow by pairs.
        cur = rng.choice(bases)
        T0 = rng.choice([0.5, 1.0, 2.0])
        while time.monotonic() < deadline and cur[0] + 2 <= mb:
            res = _augment(cur[0], cur[1], d, D, rng, deadline, T0=T0)
            if res is None:
                break
            if not lib.is_valid(res[0], res[1], d, D):
                break
            cur = res
            if cur[0] > best[0]:
                best = cur
    return best
