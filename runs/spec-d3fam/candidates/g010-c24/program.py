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


def _scan(n, adj, D):
    """Return (ordered count of pairs at distance > D, list of vertices that miss some vertex).

    Bitmask BFS of depth D from every vertex. The vertex list drives the defect-focused
    proposals in the annealer below.
    """
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    count = 0
    bad = []
    for v in range(n):
        miss = n - reach[v].bit_count()
        if miss:
            count += miss
            bad.append(v)
    return count, bad


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _anneal(N, adj, E, D, rng, deadline, max_steps):
    """Defect-focused 2-switch annealing.

    A 2-switch (a,b),(c,e) -> (a,e),(c,b) keeps all degrees and bipartiteness.
    With probability 0.7 the first edge of the switch is drawn from edges touching a
    vertex that currently misses some other vertex (a defect-focused proposal); otherwise
    it is uniform. Returns the edge list once no pair is at distance > D, else None.
    """
    M = len(E)
    cur, bad = _scan(N, adj, D)
    T = 0.6
    steps = 0
    while cur > 0:
        if steps >= max_steps or time.monotonic() >= deadline:
            return None
        steps += 1
        badset = set(bad)
        i = -1
        if badset and rng.random() < 0.7:
            cand = [k for k, (x, y) in enumerate(E) if x in badset or y in badset]
            if cand:
                i = rng.choice(cand)
        if i < 0:
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
        new, nbad = _scan(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur, bad = new, nbad
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return E


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices (a point P and a line L) without changing any old degree.

    Step 1: pick a random matching of d edges (a_i, b_i) with a_i in colour 0 and b_i in
            colour 1; replace each by (a_i, P) and (b_i, L). P and L get degree d.
    Step 2: defect-focused annealing with 2-switches (see _anneal).
    Returns (n+2, edges) with diameter <= D, or None.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1                      # P has colour 1, L has colour 0
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
    E = [oriented[k] for k in range(len(oriented)) if k not in picked]
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

    res = _anneal(N, adj, E, D, rng, deadline, max_steps=4000)
    if res is None:
        return None
    return N, list(res)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

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
                res = None
                # Random restarts of the matching and annealing until the deadline.
                while res is None and time.monotonic() < deadline:
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
