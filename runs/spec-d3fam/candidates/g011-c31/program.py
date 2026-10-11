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


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _reach_masks(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _count(reach, n):
    """Ordered count of vertex pairs at distance > D, from reach masks."""
    return sum(n - r.bit_count() for r in reach)


def _ball(adj, v, r):
    """Set of vertices within distance r of v."""
    seen = {v}
    cur = [v]
    for _ in range(r):
        nxt = []
        for u in cur:
            for w in adj[u]:
                if w not in seen:
                    seen.add(w)
                    nxt.append(w)
        cur = nxt
    return seen


def _random_bad_pair(N, reach, rng):
    """Pick a random ordered pair (x, y) at distance > D, or None if there is none."""
    full = (1 << N) - 1
    cands = [x for x in range(N) if reach[x] != full]
    if not cands:
        return None
    x = rng.choice(cands)
    miss = full ^ reach[x]
    bits = []
    while miss:
        lsb = miss & -miss
        bits.append(lsb.bit_length() - 1)
        miss ^= lsb
    return x, rng.choice(bits)


def _targeted(E, adj, col, x, y, rng):
    """Targeted 2-switch that gives x a new neighbour lying within distance 2 of y.

    Returns (i, j) with the switch (a,b),(c,e) -> (a,e),(c,b), or None.
    Orientation is kept: E entries are (colour0, colour1).
    """
    if col[x] == 0:
        idx = [i for i, (a, b) in enumerate(E) if a == x]
    else:
        idx = [i for i, (a, b) in enumerate(E) if b == x]
    if not idx:
        return None
    B = _ball(adj, y, 2)
    i = rng.choice(idx)
    a, b = E[i]
    cands = []
    for j, (c, e) in enumerate(E):
        if j == i:
            continue
        if col[x] == 0:
            # new edges (x, e) and (c, b); x = a
            if c != x and e in B and e not in adj[x] and b not in adj[c]:
                cands.append(j)
        else:
            # new edges (a, e) and (c, x); x = b
            if c in B and a != c and e != x and e not in adj[a] and x not in adj[c]:
                cands.append(j)
    if not cands:
        return None
    return i, rng.choice(cands)


def _random_switch(E, adj, rng):
    """Random valid 2-switch candidate (i, j), or None."""
    M = len(E)
    i = rng.randrange(M)
    j = rng.randrange(M)
    if i == j:
        return None
    a, b = E[i]
    c, e = E[j]
    if a == c or b == e or e in adj[a] or b in adj[c]:
        return None
    return i, j


def _swap(adj, a, b, c, e):
    """Remove (a,b),(c,e) and add (a,e),(c,b)."""
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    adj[a].add(e)
    adj[e].add(a)
    adj[c].add(b)
    adj[b].add(c)


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices P (colour 1) and L (colour 0) to a bipartite graph of max degree d.

    Step 1: take a matching of d edges (a_i, b_i) and replace each by (a_i, P), (b_i, L).
            Old degrees are unchanged; P and L get degree d.
    Step 2: anneal with degree-preserving 2-switches minimising pairs at distance > D.
            Each move is targeted: pick a bad pair (x, y) and give x a new neighbour
            within distance 2 of y, so the switch directly shortens the bad path.
            If no targeted move exists, a random valid switch is used.
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
    col.append(1)
    col.append(0)
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

    reach = _reach_masks(N, adj, D)
    cur = _count(reach, N)
    T = 0.5
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        pr = _random_bad_pair(N, reach, rng)
        if pr is None:
            break
        x, y = pr
        mv = _targeted(E, adj, col, x, y, rng)
        if mv is None:
            mv = _random_switch(E, adj, rng)
            if mv is None:
                continue
        i, j = mv
        a, b = E[i]
        c, e = E[j]
        _swap(adj, a, b, c, e)              # now has (a,e), (c,b)
        nreach = _reach_masks(N, adj, D)
        new = _count(nreach, N)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = nreach
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            _swap(adj, a, e, c, b)          # revert: restores (a,b), (c,e)
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
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
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
