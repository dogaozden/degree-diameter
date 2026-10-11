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
    """Ordered count of vertex pairs at distance > D, via bitmask ball growth."""
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


def _largest_pp_at_most(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _augment_once(n, edges, d, D, rng, deadline, max_iters):
    """One attempt to add two vertices (P, L) to a bipartite graph keeping max degree d.

    1. Saturate spare degree between opposite sides with random non-edges.
    2. Pick a matching of d edges (a_i, b_i); replace each by (a_i, P) and (b_i, L).
    3. Anneal with 2-switches that keep degrees and bipartiteness, minimising the number
       of ordered pairs at distance > D.
    Returns (n+2, edges) with diameter <= D, or None.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    # Use spare degree first.
    left = [v for v in range(n) if col[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if col[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)

    E = [(u, v) for u in range(n) if col[u] == 0 for v in adj[u]]
    rng.shuffle(E)
    used, pick = set(), []
    for idx, (a, b) in enumerate(E):
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    N = n + 2
    picked = set(pick)
    newE = [E[i] for i in range(len(E)) if i not in picked]
    for idx in pick:
        a, b = E[idx]          # a has colour 0, b has colour 1
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)
        newE.append((a, P))
        newE.append((L, b))
    E = newE

    M = len(E)
    cur = _bad_count(N, adj, D)
    it = 0
    while cur > 0 and it < max_iters:
        if time.monotonic() >= deadline:
            return None
        it += 1
        T = max(0.3, 2.0 * (1.0 - it / max_iters))
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # 2-switch: (a,b),(c,e) -> (a,e),(c,b)
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    if cur == 0:
        return N, list(E)
    return None


def _augment(n, edges, d, D, rng, deadline):
    """Repeated randomized attempts to add two vertices until success or deadline."""
    while time.monotonic() < deadline:
        res = _augment_once(n, edges, d, D, rng, deadline, 2000)
        if res is not None:
            return res
    return None


def _grow(n, edges, d, D, rng, deadline, mb):
    """Grow a valid graph by two vertices at a time while time and the Moore bound allow."""
    cur = (n, edges)
    while time.monotonic() < deadline and cur[0] + 2 <= mb:
        res = _augment(cur[0], cur[1], d, D, rng, deadline)
        if res is None:
            break
        if not lib.is_valid(res[0], res[1], d, D):
            break
        cur = res
    return cur


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    mb = _moore(d, D)

    # Structured bases (diameter 3, so valid for every D >= 3).
    bases = []
    if D >= 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            bases.append(lib.projective_plane_incidence(d - 1))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                bases.append(lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass
        q = _largest_pp_at_most(d - 1)
        if q is not None:
            bases.append(lib.projective_plane_incidence(q))

    valid = []
    for n0, e0 in bases:
        if lib.is_valid(n0, e0, d, D):
            valid.append((n0, e0))
            consider(n0, e0)
    valid.sort(key=lambda b: -b[0])

    # Grow each base, splitting the remaining time evenly.
    for idx, (n0, e0) in enumerate(valid):
        now = time.monotonic()
        share = (deadline - now) / (len(valid) - idx)
        res = _grow(n0, e0, d, D, rng, now + share, mb)
        consider(res[0], res[1])

    # Random Haar search when no structured base exists or for larger D.
    if not valid or D >= 4:
        m, misses = d + 1, 0
        while time.monotonic() < deadline and misses < 10:
            S = _search_haar(d, D, m, rng, min(deadline, time.monotonic() + 2.0), 120)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
