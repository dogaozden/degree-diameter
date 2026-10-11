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


def _reach(n, adj, D):
    """Bitmask of the radius-D ball around every vertex."""
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


def _bad_from_reach(reach, n):
    """Ordered count of vertex pairs at distance > D, from precomputed balls."""
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


def _add_pair(n, adj, col, d, rng):
    """Add a point P (colour 1) and a line L (colour 0) by taking a random matching of d edges
    (a_i, b_i) and replacing each with (a_i, P) and (b_i, L). Old degrees are unchanged."""
    oriented = []
    for u in range(n):
        for v in adj[u]:
            if u < v:
                oriented.append((u, v) if col[u] == 0 else (v, u))
    rng.shuffle(oriented)
    used, pick = set(), []
    for a, b in oriented:
        if a not in used and b not in used:
            pick.append((a, b))
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None
    P, L = n, n + 1
    nadj = [set(s) for s in adj] + [set(), set()]
    for a, b in pick:
        nadj[a].discard(b)
        nadj[b].discard(a)
        nadj[a].add(P)
        nadj[P].add(a)
        nadj[b].add(L)
        nadj[L].add(b)
    ncol = list(col) + [1, 0]
    return n + 2, nadj, ncol


def _propose(x, y, adj, col, rng):
    """Directed 2-switch aimed at the bad pair (x, y).

    Opposite colours: remove (x,a),(c,y); add (x,y),(c,a). Makes x and y adjacent.
    Same colour:      remove (x,a),(c,e); add (x,e),(c,a) where e is a neighbour of y.
                      Makes x and y share the neighbour e.
    Both moves keep every degree and the bipartition.
    Returns (removals, additions) or None.
    """
    if not adj[x] or not adj[y]:
        return None
    a = rng.choice(tuple(adj[x]))
    if col[x] != col[y]:
        c = rng.choice(tuple(adj[y]))
        if c == x or a == y or c in adj[a]:
            return None
        return ((x, a), (c, y)), ((x, y), (c, a))
    e = rng.choice(tuple(adj[y]))
    cs = [c for c in adj[e] if c != y]
    if not cs:
        return None
    c = rng.choice(cs)
    if e in adj[x] or a == e or c == x or c in adj[a]:
        return None
    return ((x, a), (c, e)), ((x, e), (c, a))


def _set_edges(adj, remove, add):
    for u, v in remove:
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in add:
        adj[u].add(v)
        adj[v].add(u)


def _anneal(N, adj, col, D, rng, deadline):
    """Anneal with directed switches toward bad pairs until no pair is at distance > D.
    Modifies adj in place. Returns True on success, False on timeout."""
    full = (1 << N) - 1
    reach = _reach(N, adj, D)
    cur = _bad_from_reach(reach, N)
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-3)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        x = rng.randrange(N)
        miss = full ^ reach[x]
        if not miss:
            continue
        cand = [v for v in range(N) if (miss >> v) & 1]
        y = rng.choice(cand)
        mv = _propose(x, y, adj, col, rng)
        if mv is None:
            continue
        rem, add = mv
        _set_edges(adj, rem, add)
        new_reach = _reach(N, adj, D)
        new = _bad_from_reach(new_reach, N)
        frac = (time.monotonic() - t_start) / span
        T = 0.6 * (1.0 - frac) + 0.02
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur, reach = new, new_reach
        else:
            _set_edges(adj, add, rem)
    return True


def _attempt(n, edges, d, D, rng, deadline):
    """Try to grow a valid graph by two vertices. Returns (n+2, edges) or None."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)
    pr = _add_pair(n, adj, col, d, rng)
    if pr is None:
        return None
    N, nadj, ncol = pr
    if not _anneal(N, nadj, ncol, D, rng, deadline):
        return None
    out = [(u, v) for u in range(N) for v in nadj[u] if u < v]
    if lib.is_valid(N, out, d, D):
        return N, out
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit)
    rng = random.Random(seed)

    # Structured bases for D = 3.
    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)

    if base is not None:
        n, edges = base
        if lib.is_valid(n, edges, d, D):
            cur = (n, edges)
            mb = _moore(d, D)
            while cur[0] + 2 <= mb:
                if time.monotonic() >= deadline - 0.5:
                    break
                res = None
                for _ in range(3):
                    left = deadline - time.monotonic()
                    if left <= 0.5:
                        break
                    res = _attempt(cur[0], cur[1], d, D, rng,
                                   time.monotonic() + 0.5 * left)
                    if res is not None:
                        break
                if res is None:
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
