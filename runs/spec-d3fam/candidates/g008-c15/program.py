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


def _reach(N, adj, D):
    """Bitmask of the ball of radius D around every vertex."""
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


def _bad_from_reach(N, reach):
    """Ordered count of pairs at distance > D."""
    return sum(N - r.bit_count() for r in reach)


def _apply(adj, rem, add):
    """Remove the pairs in rem and insert the pairs in add (in place)."""
    for u, v in rem:
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in add:
        adj[u].add(v)
        adj[v].add(u)


def _propose_repair(N, adj, col, maskC, reach, rng):
    """Guided move: pick a far-apart pair (x, y) of opposite colours and 2-switch
    (x,a),(c,y) -> (x,y),(c,a). This creates a direct edge x-y and keeps degrees and bipartiteness.
    Returns (removed, added) or None."""
    full = (1 << N) - 1
    for _ in range(20):
        x = rng.randrange(N)
        cand = (full & ~reach[x]) & maskC[1 - col[x]]
        if not cand:
            continue
        bits = [i for i in range(N) if (cand >> i) & 1]
        y = rng.choice(bits)
        if not adj[x] or not adj[y]:
            continue
        a = rng.choice(tuple(adj[x]))   # colour of a equals colour of y
        c = rng.choice(tuple(adj[y]))   # colour of c equals colour of x
        if a in adj[c]:
            continue
        return [(x, a), (c, y)], [(x, y), (c, a)]
    return None


def _propose_switch(N, adj, col, rng):
    """Random degree-preserving 2-switch, orientation chosen so bipartiteness is kept."""
    for _ in range(20):
        a = rng.randrange(N)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.randrange(N)
        if c == a or col[c] != col[a] or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if b == e or e in adj[a] or b in adj[c]:
            continue
        return [(a, b), (c, e)], [(a, e), (c, b)]
    return None


def _anneal(N, adj, col, D, rng, deadline, t_start):
    """Anneal with a mix of guided repair moves and random switches until diameter <= D.
    Mutates adj. Returns the edge list on success, None on timeout."""
    maskC = [0, 0]
    for v in range(N):
        maskC[col[v]] |= 1 << v
    reach = _reach(N, adj, D)
    cur = _bad_from_reach(N, reach)
    span = max(1e-6, deadline - t_start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - t_start) / span)
        T = 2.0 * (1.0 - frac) + 0.15
        if rng.random() < 0.8:
            move = _propose_repair(N, adj, col, maskC, reach, rng)
        else:
            move = _propose_switch(N, adj, col, rng)
        if move is None:
            continue
        rem, add = move
        _apply(adj, rem, add)
        new_reach = _reach(N, adj, D)
        new = _bad_from_reach(N, new_reach)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = new_reach
        else:
            _apply(adj, add, rem)
    return [(u, v) for u in range(N) for v in adj[u] if u < v]


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices (point P, line L) using a d-matching and guided annealing.
    Returns (n+2, edges) or None."""
    t_start = time.monotonic()
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1           # P colour 1, L colour 0
    adj.append(set())
    adj.append(set())
    col.extend([1, 0])
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

    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)

    out = _anneal(N, adj, col, D, rng, deadline, t_start)
    if out is None:
        return None
    return N, out


def _haar_fallback(d, D, rng, deadline):
    """Random Haar graphs (parent approach), used when no structured base applies."""
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
            try:
                while time.monotonic() < deadline and cur[0] + 2 <= mb:
                    res = _augment(cur[0], cur[1], d, D, rng, deadline)
                    if res is None:
                        break
                    if not lib.is_valid(res[0], res[1], d, D):
                        break
                    cur = res
            except Exception:
                pass
            return cur

    return _haar_fallback(d, D, rng, deadline)
