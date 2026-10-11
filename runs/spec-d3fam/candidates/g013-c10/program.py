import math
import random
import time

import lib


def _adj_sets(n, edges):
    """Adjacency as a list of sets."""
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


def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance > D. Zero means the diameter is at most D."""
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


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r in the graph."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _cover(cands, ball, full, d):
    """Greedy cover of `full` by at most d candidates; None if the cover fails."""
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        best = max(pool, key=lambda s: (ball[s] & ~covered).bit_count())
        if (ball[best] & ~covered) == 0:
            break
        pool.remove(best)
        chosen.append(best)
        covered |= ball[best]
    return chosen if covered == full else None


def _cover_grow(n, edges, d, D, deadline):
    """Add vertices whose neighbourhoods cover every vertex within distance D-1.

    A new vertex v joined to such a cover keeps the graph bipartite and diameter <= D,
    since old distances can only shrink. Only spare-degree vertices are used.
    """
    edges = list(edges)
    adj = _adj_sets(n, edges)
    col = _color(n, adj)
    while time.monotonic() < deadline:
        deg = [len(a) for a in adj]
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if col[s] == c and deg[s] < d]
            chosen = _cover(cands, ball, full, d)
            if chosen:
                v = n
                n += 1
                adj.append(set())
                col.append(1 - c)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].add(v)
                    adj[v].add(s)
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    """Join deficient opposite-colour vertices; this only shrinks distances."""
    adj = _adj_sets(n, edges)
    col = _color(n, adj)
    deg = [len(a) for a in adj]
    L = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R if b not in adj[a]]
    rng.shuffle(pairs)
    E = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            deg[a] += 1
            deg[b] += 1
            E.append((a, b))
    return E


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices (a point P and a line L) by degree-preserving 2-switches.

    Pick a matching of d edges (a_i, b_i) with a_i on colour 0 and b_i on colour 1.
    Replace each by (a_i, P) and (L, b_i). Degrees of old vertices are unchanged,
    and P, L reach degree d. Then anneal with switches (a,b),(c,e) -> (a,e),(c,b),
    which keep degrees and bipartiteness, until the bad-pair count reaches zero.
    Returns (n+2, edges) or None.
    """
    adj = _adj_sets(n, edges)
    col = _color(n, adj)
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
    P, L = n, n + 1          # P has colour 1, L has colour 0
    N = n + 2
    adj.append(set())
    adj.append(set())
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
    T = 1.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
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
    return N, E


def _haar_fallback(d, D, rng, deadline):
    """Random Haar-graph search, used when no structured base applies."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Structured base for D >= 3 (diameter-3 incidence families, record constructions).
    base = None
    try:
        q = d - 1
        if D >= 3 and q >= 2 and lib.is_prime_power(q):
            base = lib.projective_plane_incidence(q)          # order 2(q^2+q+1), degree q+1
        elif D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            base = lib.araujo_lopez_graph(d - 2)              # order 2(q^2+q+5), degree q+2 = d
    except Exception:
        base = None

    if base is None or not lib.is_valid(base[0], base[1], d, D):
        best = _haar_fallback(d, D, rng, deadline)
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    best = base
    cur_n, cur_e = base

    # Phase 1: cover-based growth, then saturation of leftover degree.
    cover_deadline = start + 0.15 * time_limit
    gn, ge = _cover_grow(cur_n, cur_e, d, D, cover_deadline)
    ge = _saturate(gn, ge, d, rng)
    if gn > cur_n and lib.is_valid(gn, ge, d, D):
        cur_n, cur_e = gn, ge
        best = (cur_n, cur_e)

    # Phase 2: repeated two-vertex annealed augmentation until time or the Moore bound stops it.
    mb = _moore(d, D)
    fails = 0
    while time.monotonic() < deadline and cur_n + 2 <= mb and fails < 200:
        res = _augment(cur_n, cur_e, d, D, rng, deadline)
        if res is None:
            fails += 1
            continue
        if lib.is_valid(res[0], res[1], d, D):
            cur_n, cur_e = res
            best = res
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
