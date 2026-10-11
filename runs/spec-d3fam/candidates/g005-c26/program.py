"""Targeted-switch augmentation for bipartite graphs of diameter D = 3.

New idea (not in the parent): instead of 2-switches on uniformly random edge pairs,
each move is aimed at a specific far pair. Pick a vertex x and a vertex w at distance
> D from it. Pick a neighbour a of x and a vertex e at distance 1 (or 2, when the colours
of x and w agree) from w. Remove (a,b) and (c,e) for random neighbours b of a and c of e,
then add (a,e) and (c,b). This preserves all degrees and bipartiteness, and creates a short
x-w route through a and e. Moves are accepted by simulated annealing on the ordered count
of pairs at distance > D.
"""
import math
import random
import time

import lib


def _adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _colour(n, adj):
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


def _reach(N, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
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


def _bad(reach, N):
    return sum(N - r.bit_count() for r in reach)


def _targeted_anneal(N, adj, col, D, rng, deadline):
    """Anneal with targeted 2-switches until every pair is within distance D.

    Returns True on success, False if the deadline passes first. Mutates adj in place.
    """
    full = (1 << N) - 1
    reach = _reach(N, adj, D)
    cur = _bad(reach, N)
    T = 0.8
    while cur > 0:
        if time.monotonic() >= deadline:
            return False
        bad = [x for x in range(N) if reach[x].bit_count() < N]
        x = rng.choice(bad)
        missing = full & ~reach[x]
        cands = [w for w in range(N) if (missing >> w) & 1]
        w = rng.choice(cands)

        # e must have colour opposite to a, where a is a neighbour of x.
        if col[x] != col[w]:
            ring = list(adj[w])
        else:
            s = set()
            for u in adj[w]:
                s |= adj[u]
            s.discard(w)
            ring = list(s)
        if not ring or not adj[x]:
            continue
        e = rng.choice(ring)
        a = rng.choice(list(adj[x]))
        if e in adj[a] or a == e:
            continue
        b = rng.choice(list(adj[a]))
        c = rng.choice(list(adj[e]))
        if a == c or b == e or b in adj[c]:
            continue
        if b == c:
            continue

        # Apply 2-switch: (a,b),(c,e) -> (a,e),(c,b).
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)

        new_reach = _reach(N, adj, D)
        new = _bad(new_reach, N)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = new_reach
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return True


def _augment(n, edges, d, D, rng, deadline):
    """Add a point P and a line L with degree d each, by degree-preserving edge moves.

    Pick a matching of d edges (a_i, b_i) with a_i colour 0 and b_i colour 1. Replace each
    by (a_i, P) and (b_i, L). Then run targeted annealing. Returns (n+2, edges) or None.
    """
    adj = _adjacency(n, edges)
    col = _colour(n, adj)
    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    col.append(1)  # P: neighbours have colour 0
    col.append(0)  # L: neighbours have colour 1
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

    if not _targeted_anneal(N, adj, col, D, rng, deadline):
        return None
    out = [(u, v) for u in range(N) for v in adj[u] if u < v]
    return N, out


def _moore(d, D):
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

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
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, deadline)
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            return cur

    # Fallback: random Haar graphs.
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
