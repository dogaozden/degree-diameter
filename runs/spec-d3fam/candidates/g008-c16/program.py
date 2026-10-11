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


def _augment_once(n, edges, d, D, rng, deadline, max_iters):
    """One attempt to add a point P and a line L using degree-preserving 2-switches.

    Removes a matching of d edges (a_i, b_i) and replaces them by (a_i, P), (b_i, L).
    Then anneals over bipartite 2-switches minimising pairs at distance > D.
    Returns (n + 2, edges) on success, otherwise None.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1          # P has colour 1, L has colour 0
    adj.append(set())
    adj.append(set())
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

    M = len(E)
    cur = _bad_count(N, adj, D)
    for it in range(max_iters):
        if cur == 0:
            break
        if (it & 63) == 0 and time.monotonic() >= deadline:
            return None
        T = 0.05 + 0.95 * (1.0 - it / max_iters)
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
    if cur == 0:
        return N, list(E)
    return None


def _augment(n, edges, d, D, rng, deadline):
    """Repeated randomized restarts of _augment_once until success or deadline."""
    while time.monotonic() < deadline:
        res = _augment_once(n, edges, d, D, rng, deadline, max_iters=30000)
        if res is not None:
            return res
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(res):
        nonlocal best
        n, e = res
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    base = None
    if D == 3:
        cands = []
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            cands.append(lib.projective_plane_incidence(q))      # order 2(q^2+q+1), degree d
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))      # order 2(q^2+q+5), degree d
            except Exception:
                pass
        valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
        if valid:
            base = max(valid, key=lambda c: c[0])
            consider(base)
            cur = base
            mb = _moore(d, D)
            # Grow by two vertices at a time while time and the Moore bound allow.
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, deadline)
                if res is None or not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
                consider(cur)

    # Haar-graph random search: used when no structured base exists, or for D >= 4.
    if base is None or D >= 4:
        m, misses = d + 1, 0
        while time.monotonic() < deadline and misses < 10:
            found = None
            for _ in range(30):
                if time.monotonic() >= deadline:
                    break
                S = [0] + rng.sample(range(1, m), d - 1)
                n, e = lib.haar_graph(m, S)
                if lib.within_diameter(n, e, D):
                    found = (n, e)
                    break
            if found is not None:
                consider(found)
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
