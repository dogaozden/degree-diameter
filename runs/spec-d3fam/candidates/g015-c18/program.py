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
    """Ordered count of vertex pairs at distance > D (bitmask BFS from adjacency sets)."""
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


def _augment(n, edges, d, D, rng, deadline, T0=1.0, T_min=0.02, cool=0.998):
    """Add two vertices (a point P and a line L) by degree-preserving edge switches.

    Step 1: choose a matching of d edges (a_i, b_i) with a_i in colour 0 and b_i in colour 1;
            replace each by (a_i, P) and (b_i, L). Old degrees are unchanged; P, L get degree d.
    Step 2: anneal with 2-switches (a,b),(c,e) -> (a,e),(c,b). These keep all degrees and
            bipartiteness, and minimise the number of ordered pairs at distance > D.
            The temperature cools geometrically from T0 towards T_min (restarts re-heat it).
    Returns (n+2, edges) with diameter <= D, or None if the search fails before the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1                      # P has colour 1 (neighbours colour 0); L has colour 0
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
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        T = max(T_min, T * cool)
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


def _structured_base(d, D):
    """Return a valid structured base (n, edges) for D = 3 when one applies, else None."""
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)      # order 2(q^2+q+1), degree q+1
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)          # order 2(q^2+q+5), degree q+2 = d
    return None


def _grow_from(n, edges, d, D, rng, deadline):
    """Repeatedly add vertex pairs with restarted, re-heated annealing; return the largest valid graph."""
    best = (n, edges)
    mb = _moore(d, D)
    fails = 0
    while time.monotonic() < deadline and best[0] + 2 <= mb and fails < 6:
        # Vary the annealing schedule across attempts to diversify the search.
        T0 = rng.choice([0.5, 1.0, 2.0, 4.0])
        cool = rng.choice([0.995, 0.998, 0.999])
        res = _augment(best[0], best[1], d, D, rng, deadline, T0=T0, cool=cool)
        if res is None:
            fails += 1
            continue
        if not lib.is_valid(res[0], res[1], d, D):
            fails += 1
            continue
        best = res
        fails = 0
    return best


def _haar_fallback(d, D, rng, deadline):
    """Random Haar graphs (safe fallback, always valid)."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    base = _structured_base(d, D)
    if base is not None:
        n, edges = base
        if lib.is_valid(n, edges, d, D):
            cur = _grow_from(n, edges, d, D, rng, deadline)
            if lib.is_valid(cur[0], cur[1], d, D):
                return cur
            # Should not happen; fall back to the validated base.
            return (n, edges)

    result = _haar_fallback(d, D, rng, deadline)
    if lib.is_valid(result[0], result[1], d, D):
        return result
    return lib.haar_graph(d, range(d))
