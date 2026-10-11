import math
import random
import time

import lib


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets (DFS from each unseen vertex)."""
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
    """Ordered count of vertex pairs at distance > D (bitmask BFS), computed from adjacency sets."""
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


def _anneal(N, adj, E, D, rng, deadline, max_iter):
    """Anneal degree-preserving 2-switches on the edge list E (oriented colour0 -> colour1).

    The objective is the number of ordered pairs at distance > D. The temperature decays
    linearly over max_iter steps. adj and E are updated in place. Returns True iff diameter <= D.
    """
    M = len(E)
    cur = _bad_count(N, adj, D)
    for it in range(max_iter):
        if cur == 0:
            return True
        if (it & 127) == 0 and time.monotonic() >= deadline:
            return False
        T = 0.02 + 0.8 * (1.0 - it / max_iter)
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # 2-switch: (a,b),(c,e) -> (a,e),(c,b); keeps degrees and bipartiteness.
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
    return cur == 0


def _augment(n, edges, d, D, rng, deadline, max_iter=15000):
    """Add two new vertices (a point P and a line L) by restarted annealing.

    Each restart draws a fresh random matching of d edges (a_i, b_i) with a_i in colour 0 and
    b_i in colour 1, and replaces each by (a_i, P) and (b_i, L). Old degrees are preserved, and
    P and L get degree d. Restarts continue until the anneal reaches diameter <= D or time runs out.
    Returns (n+2, edges), or None.
    """
    base_adj = [set() for _ in range(n)]
    for u, v in edges:
        base_adj[u].add(v)
        base_adj[v].add(u)
    col = _color(n, base_adj)
    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
    N = n + 2
    P, L = n, n + 1

    while time.monotonic() < deadline:
        order = list(range(len(oriented)))
        rng.shuffle(order)
        used, pick = set(), []
        for idx in order:
            a, b = oriented[idx]
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
        adj = [set(s) for s in base_adj] + [set(), set()]
        for idx in pick:
            a, b = oriented[idx]
            adj[a].discard(b); adj[b].discard(a)
            adj[a].add(P); adj[P].add(a)
            adj[b].add(L); adj[L].add(b)
            E.append((a, P))
            E.append((L, b))
        if _anneal(N, adj, E, D, rng, deadline, max_iter):
            return N, list(E)
    return None


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
