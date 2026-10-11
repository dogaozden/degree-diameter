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
    """Ordered count of vertex pairs at distance > D (bitmask BFS). Zero iff diameter <= D and connected."""
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


def _setup_add(n, edges, d, rng):
    """Attach a new point P and new line L by a random matching of d edges.

    Each matched edge (a, b) becomes (a, P) and (b, L); old degrees are unchanged,
    P and L get degree d. Returns (N, adj, E) with E holding (colour0, colour1) pairs,
    or None if no matching of size d exists in this random order.
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
    return N, adj, E


def _anneal(N, adj, E, D, rng, deadline, max_steps):
    """Degree-preserving 2-switch annealing minimising bad pairs.

    Switch (a,b),(c,e) -> (a,e),(c,b) keeps all degrees and bipartiteness because
    a, c have colour 0 and b, e have colour 1 in the stored orientation.
    Temperature decays geometrically. Returns the edge list on success, else None.
    """
    M = len(E)
    cur = _bad_count(N, adj, D)
    T = 1.0
    steps = 0
    while cur > 0:
        if steps >= max_steps or time.monotonic() >= deadline:
            return None
        steps += 1
        T = max(0.05, T * 0.9995)
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
    return list(E)


def _attempt_add(n, edges, d, D, rng, deadline):
    """Try several random matchings and anneals to add two vertices. Returns (n+2, edges) or None."""
    while time.monotonic() < deadline:
        setup = _setup_add(n, edges, d, rng)
        if setup is None:
            return None
        N, adj, E = setup
        out = _anneal(N, adj, E, D, rng, deadline, max_steps=4000)
        if out is not None:
            return N, out
    return None


def _grow(n, edges, d, D, rng, deadline):
    """Repeatedly add two vertices while time, the Moore bound and validity allow."""
    mb = _moore(d, D)
    cur = (n, list(edges))
    while cur[0] + 2 <= mb and time.monotonic() < deadline:
        res = _attempt_add(cur[0], cur[1], d, D, rng, deadline)
        if res is None or not lib.is_valid(res[0], res[1], d, D):
            break
        cur = res
    return cur


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    # Structured bases for D = 3.
    base = None
    q = d - 1
    try:
        if D == 3 and q >= 2 and lib.is_prime_power(q):
            base = lib.projective_plane_incidence(q)      # order 2(q^2+q+1), degree q+1
        elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            base = lib.araujo_lopez_graph(d - 2)          # order 2(q^2+q+5), degree q+2 = d
    except Exception:
        base = None

    if base is not None:
        n, edges = base
        if lib.is_valid(n, edges, d, D):
            try:
                grown = _grow(n, edges, d, D, rng, deadline)
                if grown[0] >= n and lib.is_valid(grown[0], grown[1], d, D):
                    return grown
            except Exception:
                pass
            return n, edges

    # Fallback: random Haar graphs. K_{d,d} is always valid.
    best = lib.haar_graph(d, range(d))
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
