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


def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance > D (bitmask BFS), computed from adjacency sets."""
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


def _switch(adj, a, b, c, e):
    """2-switch: remove (a,b),(c,e) and add (a,e),(c,b). Degrees and bipartiteness are preserved."""
    adj[a].discard(b); adj[b].discard(a)
    adj[c].discard(e); adj[e].discard(c)
    adj[a].add(e); adj[e].add(a)
    adj[c].add(b); adj[b].add(c)


def _key(u, v):
    return (u, v) if u < v else (v, u)


def _tabu_augment(n, edges, d, D, rng, deadline):
    """Add a point P and a line L with degree d each, then repair by tabu search over 2-switches.

    Setup: pick a matching of d edges (a_i, b_i) and replace each by (a_i, P) and (b_i, L).
    Repair: each iteration samples a batch of candidate 2-switches, applies the best
    non-tabu one (aspiration allows a tabu move that beats the best seen), and makes the
    edges it removes tabu for a short random tenure. Accepts the best state ever seen.
    Returns (n+2, edges) with diameter <= D, or None if no valid state is found by the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1                      # P has colour 1 (neighbours colour 0); L has colour 0
    adj.append(set())
    adj.append(set())
    N = n + 2

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

    M = len(E)
    cur = _bad_count(N, adj, D)
    best, best_E = cur, list(E)
    tabu = {}
    it = 0
    CAND = 40

    while cur > 0:
        if time.monotonic() >= deadline:
            break
        it += 1
        move = None
        move_val = None
        for _ in range(CAND):
            if time.monotonic() >= deadline:
                break
            i = rng.randrange(M)
            j = rng.randrange(M)
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or e in adj[a] or b in adj[c]:
                continue
            is_tabu = tabu.get(_key(a, e), -1) >= it or tabu.get(_key(c, b), -1) >= it
            _switch(adj, a, b, c, e)
            val = _bad_count(N, adj, D)
            _switch(adj, a, e, c, b)  # revert
            if is_tabu and val >= best:
                continue
            if move_val is None or val < move_val:
                move_val = val
                move = (i, j)
        if move is None:
            continue
        i, j = move
        a, b = E[i]
        c, e = E[j]
        _switch(adj, a, b, c, e)
        E[i] = (a, e)
        E[j] = (c, b)
        tenure = 7 + rng.randrange(5)
        tabu[_key(a, b)] = it + tenure
        tabu[_key(c, e)] = it + tenure
        cur = move_val
        if cur < best:
            best = cur
            best_E = list(E)

    if best == 0:
        return N, best_E
    return None


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
            # Repeatedly try to grow by two vertices while time and the Moore bound allow.
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _tabu_augment(cur[0], cur[1], d, D, rng, deadline)
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
