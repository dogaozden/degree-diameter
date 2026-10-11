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
    """Ordered count of vertex pairs at distance > D, via bitmask reachability."""
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


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices P (colour 1) and L (colour 0) by degree-preserving edge moves,
    then anneal with 2-switches to minimise pairs at distance > D.
    Returns (n + 2, edges) or None if no valid graph is found before the deadline."""
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
    T = 1.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # 2-switch: (a,b),(c,e) -> (a,e),(c,b); preserves degrees and bipartiteness.
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


def _saturate(n, edges, d, rng):
    """Add edges between deficient opposite-side vertices. Never increases distances."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    col = _color(n, adj)
    left = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, edges


def _grow(n, edges, d, D, deadline, rng):
    """Repeatedly add two vertices by augment, with restarts, while time and Moore bound allow."""
    cur = (n, list(edges))
    mb = _moore(d, D)
    while time.monotonic() < deadline and cur[0] + 2 <= mb:
        now = time.monotonic()
        attempt_deadline = min(deadline, now + 0.3 * (deadline - now) + 2.0)
        res = _augment(cur[0], cur[1], d, D, rng, attempt_deadline)
        if res is None:
            continue
        if not lib.is_valid(res[0], res[1], d, D):
            continue
        cur = res
    return cur


def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, then saturated."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Candidate bases for D >= 3.
    bases = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            if lib.is_valid(n, e, d, D):
                bases.append((n, e))
        except (ValueError, StopIteration, KeyError):
            pass
    if D >= 3:
        pg = _pg_base(d)
        if pg is not None:
            n, e = pg
            if lib.is_prime_power(d - 1) or not bases:
                # Saturate to use leftover degree (no-op when already d-regular).
                n, e = _saturate(n, e, d, rng)
            bases.append((n, e))

    for n, e in bases:
        consider(n, e)

    if not bases:
        return best

    # Grow the largest valid base by augmenting; keep the best result.
    bases.sort(key=lambda g: -g[0])
    n0, e0 = bases[0]
    if lib.is_valid(n0, e0, d, D):
        n1, e1 = _grow(n0, e0, d, D, deadline, rng)
        consider(n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
