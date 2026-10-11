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
    """Ordered count of vertex pairs at distance > D (bitmask BFS over adjacency sets)."""
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
    """Add two vertices (a point P and a line L) by degree-preserving 2-switch annealing.

    A matching of d edges (a_i, b_i), a_i in colour 0 and b_i in colour 1, is replaced by
    (a_i, P) and (L, b_i). Old degrees are unchanged, P and L get degree d. Then 2-switches
    (a,b),(c,e) -> (a,e),(c,b) keep degrees and bipartiteness while minimising the number
    of pairs at distance > D. Returns (n+2, edges), or None if the search fails by deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1          # P has colour 1 (neighbours colour 0); L has colour 0
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


def _grow(n, edges, d, D, rng, deadline):
    """Repeatedly add two vertices by annealed switching while time and the Moore bound allow."""
    cur = (n, list(edges))
    mb = _moore(d, D)
    fails = 0
    while time.monotonic() < deadline and cur[0] + 2 <= mb and fails < 3:
        now = time.monotonic()
        slice_end = min(deadline, now + max(4.0, (deadline - now) / 3))
        res = _augment(cur[0], cur[1], d, D, rng, slice_end)
        if res is None or not lib.is_valid(res[0], res[1], d, D):
            fails += 1
            continue
        cur = res
        fails = 0
    return cur


def _search_haar(d, D, deadline, rng):
    """Random Haar-graph search: returns the largest valid Haar graph found, or None."""
    best = None
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Always-valid fallback for D >= 2: K_{d,d}, diameter 2.
    kdd = lib.haar_graph(d, range(d))
    cands = [kdd]

    if D >= 3:
        # Moore-optimal incidence graph of PG(2, d-1).
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            cands.append(lib.projective_plane_incidence(d - 1))
        # Araujo-Pardo & Lopez record family for d-2 a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass
        # Plain projective plane with largest prime power q <= d-1.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break

    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    best = max(valid, key=lambda c: c[0])
    best_is_kdd = best is kdd

    if D >= 3 and not best_is_kdd:
        # Annealed vertex growth on the best structured base.
        grown = _grow(best[0], best[1], d, D, rng, deadline)
        if lib.is_valid(grown[0], grown[1], d, D) and grown[0] > best[0]:
            best = grown

    if best_is_kdd and D >= 3:
        h = _search_haar(d, D, deadline, rng)
        if h is not None and h[0] > best[0] and lib.is_valid(h[0], h[1], d, D):
            best = h

    if not lib.is_valid(best[0], best[1], d, D):
        best = kdd
    return best
