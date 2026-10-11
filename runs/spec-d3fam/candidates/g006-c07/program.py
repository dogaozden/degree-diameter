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


def _reach(n, adj, D):
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


def _bad_from_reach(n, reach):
    """Ordered count of pairs at distance > D, from reach masks."""
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


def _swap(adj, E, i, j, new_i, new_j):
    """Replace edges E[i], E[j] by new_i, new_j, keeping adjacency sets in sync."""
    for u, v in (E[i], E[j]):
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in (new_i, new_j):
        adj[u].add(v)
        adj[v].add(u)
    E[i] = new_i
    E[j] = new_j


def _targeted(N, adj, E, col, reach, rng):
    """Invented 'close-pair' move: pick a cross-colour bad pair (x, y) and make x adjacent to y.

    Take an edge (x, b) and an edge (c, y), with x on colour 0 and y on colour 1, and
    replace them by (x, y) and (c, b). This keeps all degrees and bipartiteness.
    Returns (i, j, new_i, new_j) or None.
    """
    full = (1 << N) - 1
    x = y = None
    for _ in range(20):
        p = rng.randrange(N)
        miss = full & ~reach[p] & ~(1 << p)
        if not miss:
            continue
        ys = [q for q in range(N) if (miss >> q) & 1 and col[q] != col[p]]
        if ys:
            x, y = p, rng.choice(ys)
            break
    if x is None:
        return None
    if col[x] == 1:
        x, y = y, x
    bs = list(adj[x])
    if not bs:
        return None
    b = rng.choice(bs)
    cs = [c for c in adj[y] if b not in adj[c]]
    if not cs:
        return None
    c = rng.choice(cs)
    i = E.index((x, b))
    j = E.index((c, y))
    return i, j, (x, y), (c, b)


def _anneal(N, adj, E, col, D, rng, deadline):
    """Anneal with a mix of targeted close-pair moves and random 2-switches.

    Cost is the ordered number of pairs at distance > D. Degrees and bipartiteness are preserved.
    Temperature decays with elapsed time. Returns a copy of E with cost 0, or None.
    """
    reach = _reach(N, adj, D)
    cur = _bad_from_reach(N, reach)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.05, 1.5 * (1.0 - (now - t0) / span))
        if rng.random() < 0.6:
            mv = _targeted(N, adj, E, col, reach, rng)
            if mv is None:
                continue
            i, j, ni, nj = mv
        else:
            M = len(E)
            i = rng.randrange(M)
            j = rng.randrange(M)
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or e in adj[a] or b in adj[c]:
                continue
            ni, nj = (a, e), (c, b)
        oi, oj = E[i], E[j]
        _swap(adj, E, i, j, ni, nj)
        nreach = _reach(N, adj, D)
        new = _bad_from_reach(N, nreach)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            reach = nreach
            cur = new
        else:
            _swap(adj, E, i, j, oi, oj)
    if cur == 0:
        return list(E)
    return None


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices (a point P and a line L) using degree-preserving edge switches.

    Step 1: pick a matching of d edges (a_i, b_i) and replace each by (a_i, P), (b_i, L).
    Step 2: anneal with targeted and random switches until diameter <= D.
    Returns (n+2, edges) or None.
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
    col = col + [1, 0]

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

    res = _anneal(N, adj, E, col, D, rng, deadline)
    if res is None:
        return None
    return N, res


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
