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


def _bad(N, adj, D):
    """Return (ordered count of pairs at distance > D, per-vertex reach bitmasks)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach), reach


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ---------------------------------------------------------------- switch moves

def _ok_switch(adj, x, a, c, e):
    """2-switch (x,a),(c,e) -> (x,e),(c,a) is legal: no loops, no duplicate edges."""
    return x != c and a != e and e not in adj[x] and a not in adj[c]


def _switch(adj, x, a, c, e):
    adj[x].discard(a); adj[a].discard(x)
    adj[c].discard(e); adj[e].discard(c)
    adj[x].add(e); adj[e].add(x)
    adj[c].add(a); adj[a].add(c)


def _unswitch(adj, x, a, c, e):
    adj[x].discard(e); adj[e].discard(x)
    adj[c].discard(a); adj[a].discard(c)
    adj[x].add(a); adj[a].add(x)
    adj[c].add(e); adj[e].add(c)


def _random_move(adj, side0, rng):
    """Uniform random degree-preserving 2-switch between colour-0 vertices."""
    for _ in range(20):
        x = rng.choice(side0)
        a = rng.choice(list(adj[x]))
        c = rng.choice(side0)
        e = rng.choice(list(adj[c]))
        if _ok_switch(adj, x, a, c, e):
            return (x, a, c, e)
    return None


def _guided_move(adj, col, N, reach, full, bad_vertices, rng):
    """Distance-guided 2-switch aimed at one bad pair (x, y).

    Same colour: x needs a common neighbour with y, so x is joined to a neighbour e of y.
    Opposite colours: x needs a path of length 3 to y, so x is joined to e in N(N(y)).
    Only the edge (x,a) and an edge (c,e) are rewired, so all degrees are preserved.
    """
    x = rng.choice(bad_vertices)
    missing = [y for y in range(N) if y != x and not (reach[x] >> y) & 1]
    if not missing:
        return None
    y = rng.choice(missing)
    if col[x] == col[y]:
        T = set(adj[y])
    else:
        T = {e for m in adj[y] for e in adj[m]}
    cand = [e for e in T if e != x and e not in adj[x] and col[e] != col[x]]
    if not cand:
        return None
    e = rng.choice(cand)
    for _ in range(8):
        c = rng.choice(list(adj[e]))
        a = rng.choice(list(adj[x]))
        if _ok_switch(adj, x, a, c, e):
            return (x, a, c, e)
    return None


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices (a point P and a line L), then anneal with switches.

    Step 1: take a matching of d edges (a_i, b_i) and replace each by (a_i, P), (b_i, L).
            Old degrees are unchanged; P and L get degree d.
    Step 2: anneal over degree-preserving switches. About 70% of moves are distance-guided
            (aimed at a random bad pair), the rest are uniform random switches.
            The objective is the number of ordered pairs at distance > D.
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
    col.append(1)   # P: neighbours have colour 0
    col.append(0)   # L: neighbours have colour 1
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

    side0 = [v for v in range(N) if col[v] == 0]
    full = (1 << N) - 1
    cnt, reach = _bad(N, adj, D)
    T = 0.6
    while cnt > 0:
        if time.monotonic() >= deadline:
            return None
        bad_vertices = [v for v in range(N) if reach[v] != full]
        if rng.random() < 0.7:
            mv = _guided_move(adj, col, N, reach, full, bad_vertices, rng)
        else:
            mv = _random_move(adj, side0, rng)
        if mv is None:
            continue
        x, a, c, e = mv
        _switch(adj, x, a, c, e)
        new, nreach = _bad(N, adj, D)
        if new <= cnt or rng.random() < math.exp((cnt - new) / T):
            cnt, reach = new, nreach
        else:
            _unswitch(adj, x, a, c, e)
    out = [(v, u) for v in range(N) for u in adj[v] if v < u]
    return N, out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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
            fails = 0
            while time.monotonic() < deadline and cur[0] + 2 <= mb and fails < 40:
                now = time.monotonic()
                remaining = deadline - now
                chunk = max(2.0, remaining / 2.0)   # restart with a fresh matching if stuck
                res = _augment(cur[0], cur[1], d, D, rng, min(deadline, now + chunk))
                if res is None or not lib.is_valid(res[0], res[1], d, D):
                    fails += 1
                    continue
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
