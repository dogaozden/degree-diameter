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


def _reach(N, adj, D):
    """Per-vertex bitmask of vertices within distance D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


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
    """Add two vertices (point P, line L) by degree-preserving switches, annealing on bad pairs.

    New helper: focused switches. Pick an unreached pair (x, y), then choose the switch so that
    the new cross edge (p, s) has p adjacent-or-equal to x on x's side and s adjacent-or-equal to y
    on y's side. Such a switch shortens the x-y route to length <= 3. With small probability a
    random switch is used instead, to keep diversity.
    Returns (n+2, edges) with diameter <= D, or None if the search fails before the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1                      # P colour 1, L colour 0
    adj.append(set())
    adj.append(set())
    col.append(1)
    col.append(0)
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]  # (colour0, colour1)
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

    full = (1 << N) - 1
    reach = _reach(N, adj, D)
    cur = sum(N - r.bit_count() for r in reach)
    T = 0.6
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        M = len(E)

        # Pick an unreached ordered pair (x, y).
        x = rng.randrange(N)
        while reach[x] == full:
            x = rng.randrange(N)
        miss = [w for w in range(N) if not (reach[x] >> w) & 1]
        y = rng.choice(miss)

        if rng.random() < 0.85:
            Ax = {x} if col[x] == 0 else set(adj[x])   # colour-0 vertices within distance 1 of x
            By = {y} if col[y] == 1 else set(adj[y])   # colour-1 vertices within distance 1 of y
            ci = [k for k, (p, _) in enumerate(E) if p in Ax]
            cj = [k for k, (_, s) in enumerate(E) if s in By]
            if ci and cj:
                i = rng.choice(ci)
                j = rng.choice(cj)
            else:
                i = rng.randrange(M)
                j = rng.randrange(M)
        else:
            i = rng.randrange(M)
            j = rng.randrange(M)

        if i == j:
            continue
        p, q = E[i]
        r, s = E[j]
        # Switch (p,q),(r,s) -> (p,s),(r,q); keep it a simple bipartite graph.
        if p == r or q == s or s in adj[p] or q in adj[r]:
            continue

        adj[p].discard(q); adj[q].discard(p)
        adj[r].discard(s); adj[s].discard(r)
        adj[p].add(s); adj[s].add(p)
        adj[r].add(q); adj[q].add(r)

        new_reach = _reach(N, adj, D)
        new = sum(N - b.bit_count() for b in new_reach)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = new_reach
            E[i] = (p, s)
            E[j] = (r, q)
        else:
            adj[p].discard(s); adj[s].discard(p)
            adj[r].discard(q); adj[q].discard(r)
            adj[p].add(q); adj[q].add(p)
            adj[r].add(s); adj[s].add(r)
    return N, list(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    # Structured bases for D = 3.
    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)          # order 2(q^2+q+1), degree q+1
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)              # order 2(q^2+q+5), degree q+2 = d

    if base is not None:
        n, edges = base
        if lib.is_valid(n, edges, d, D):
            cur = (n, edges)
            mb = _moore(d, D)
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, deadline)
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            return cur

    # Fallback: random Haar graphs.
    best = lib.haar_graph(d, range(d))          # K_{d,d}: always valid
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
