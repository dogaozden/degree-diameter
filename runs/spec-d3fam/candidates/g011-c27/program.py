import math
import random
import time

import lib


# ----------------------------------------------------------------- basics

def _to_adj(n, edges):
    """Adjacency sets from an edge list."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


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


def _reach(n, adj, D):
    """Bitmask of the ball of radius D around every vertex."""
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


def _bad(n, reach):
    """Ordered count of vertex pairs at distance > D."""
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


def _apply(adj, rem, add):
    """Remove the edges in rem, then add the edges in add (adjacency sets only)."""
    for u, v in rem:
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in add:
        adj[u].add(v)
        adj[v].add(u)


# ------------------------------------------------- new: targeted repair moves
#
# Idea (new in this program): a bad pair (x, y) is repaired by a single
# degree-preserving 2-switch that is aimed at that pair, instead of a blind
# random switch.
#
#  * Same colour (no common neighbour yet): pick e in N(y) and c in N(e) with
#    c not in {x, y}, and a in N(x). Switch (x,a),(c,e) -> (x,e),(c,a).
#    Now x - e - y is a path of length 2.
#  * Opposite colour (no path of length 3 yet): pick a in N(x), e in N(y),
#    b in N(a) (b != x), f in N(e) (f != y). Switch (a,b),(e,f) -> (a,e),(b,f).
#    Now x - a - e - y is a path of length 3.
#
# Every move keeps degrees, the bipartition and the old neighbourhoods of x, y.

def _move_same(adj, x, y, rng):
    if not adj[x] or not adj[y]:
        return None
    e = rng.choice(tuple(adj[y]))
    cs = [c for c in adj[e] if c != x and c != y]
    if not cs:
        return None
    c = rng.choice(cs)
    a = rng.choice(tuple(adj[x]))
    if a in adj[c] or e in adj[x]:
        return None
    return [(x, a), (c, e)], [(x, e), (c, a)]


def _move_opp(adj, x, y, rng):
    if not adj[x] or not adj[y]:
        return None
    a = rng.choice(tuple(adj[x]))
    e = rng.choice(tuple(adj[y]))
    if a == y or e == x or e in adj[a]:
        return None
    bs = [b for b in adj[a] if b != x]
    fs = [f for f in adj[e] if f != y]
    if not bs or not fs:
        return None
    b = rng.choice(bs)
    f = rng.choice(fs)
    if f in adj[b] or b == e or f == a:
        return None
    return [(a, b), (e, f)], [(a, e), (b, f)]


def _random_switch(adj, col, groups, rng):
    """Ordinary 2-switch used now and then for diversification."""
    a = rng.randrange(len(adj))
    if not adj[a]:
        return None
    b = rng.choice(tuple(adj[a]))
    c = rng.choice(groups[col[a]])
    if c == a or not adj[c]:
        return None
    e = rng.choice(tuple(adj[c]))
    if e in adj[a] or b in adj[c]:
        return None
    return [(a, b), (c, e)], [(a, e), (c, b)]


# ------------------------------------------------------------ augmentation

def _attempt(n, base_adj, col_base, d, D, rng, deadline):
    """Add two vertices P (colour 1) and L (colour 0) to a valid base graph.

    P and L take over d disjoint edges (a_i, b_i): edges become (a_i, P) and (b_i, L).
    Targeted repair moves then drive the number of pairs at distance > D to zero.
    Returns the new adjacency sets, or None if the deadline passes first.
    """
    N = n + 2
    P, L = n, n + 1
    adj = [set(s) for s in base_adj] + [set(), set()]
    col = list(col_base) + [1, 0]

    oriented = [((u, v) if col_base[u] == 0 else (v, u))
                for u in range(n) for v in base_adj[u] if u < v]
    best_pick = []
    for _ in range(20):
        rng.shuffle(oriented)
        used, pick = set(), []
        for a, b in oriented:
            if a not in used and b not in used:
                pick.append((a, b))
                used.add(a)
                used.add(b)
                if len(pick) == d:
                    break
        if len(pick) > len(best_pick):
            best_pick = pick
        if len(best_pick) == d:
            break
    if len(best_pick) < 2:
        return None

    for a, b in best_pick:
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)

    groups = [[v for v in range(N) if col[v] == 0], [v for v in range(N) if col[v] == 1]]
    full = (1 << N) - 1
    reach = _reach(N, adj, D)
    cur = _bad(N, reach)
    span = max(1e-6, deadline - time.monotonic())
    T = 0.5
    it = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        it += 1
        if it % 64 == 0:
            frac = max(0.0, (deadline - time.monotonic()) / span)
            T = 0.05 + 0.6 * frac

        xs = [x for x in range(N) if reach[x] != full]
        x = rng.choice(xs)
        miss = full ^ reach[x]
        ys = [y for y in range(N) if (miss >> y) & 1]
        y = rng.choice(ys)

        if rng.random() < 0.1:
            mv = _random_switch(adj, col, groups, rng)
        elif col[x] == col[y]:
            mv = _move_same(adj, x, y, rng)
        else:
            mv = _move_opp(adj, x, y, rng)
        if mv is None:
            continue

        rem, add = mv
        _apply(adj, rem, add)
        nreach = _reach(N, adj, D)
        new = _bad(N, nreach)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = nreach
        else:
            _apply(adj, add, rem)
    return adj


# ------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.0, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
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
            cur_n, cur_edges = n, list(edges)
            mb = _moore(d, D)
            slice_len = max(5.0, budget / 3.0)
            while time.monotonic() < deadline and cur_n + 2 <= mb:
                base_adj = _to_adj(cur_n, cur_edges)
                col0 = _color(cur_n, base_adj)
                end = min(deadline, time.monotonic() + slice_len)
                adj = _attempt(cur_n, base_adj, col0, d, D, rng, end)
                if adj is None:
                    continue  # restart with a fresh random matching
                N = cur_n + 2
                new_edges = [(u, v) for u in range(N) for v in adj[u] if u < v]
                if not lib.is_valid(N, new_edges, d, D):
                    break
                cur_n, cur_edges = N, new_edges
            return cur_n, cur_edges

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
