import math
import random
import time

import lib


def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _colour(n, edges):
    adj = _adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color, adj


def _orient(edges, color):
    """Orient every edge as (side-0 vertex, side-1 vertex)."""
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


def _random_matching(A, adj, rng):
    """Random maximal bipartite matching (Kuhn's augmenting paths), as (a, b) pairs."""
    match_b = {}
    match_a = {}

    def augment(a, seen):
        for b in adj[a]:
            if b in seen:
                continue
            seen.add(b)
            if b not in match_b or augment(match_b[b], seen):
                match_b[b] = a
                match_a[a] = b
                return True
        return False

    order = list(A)
    rng.shuffle(order)
    for a in order:
        if a not in match_a:
            augment(a, set())
    return [(a, b) for a, b in match_a.items()]


def _splice(n, edges, d, color, adj, rng):
    """Add one side-0 vertex and one side-1 vertex by rewiring a random d-matching.

    Each matched edge (a, b) is removed; the new side-0 vertex joins every b and
    the new side-1 vertex joins every a. Degrees of old vertices are unchanged,
    and the new vertices have degree d.
    """
    A = [v for v in range(n) if color[v] == 0]
    pairs = _random_matching(A, adj, rng)
    if len(pairs) < d:
        return None
    chosen = rng.sample(pairs, d)
    drop = {(min(a, b), max(a, b)) for a, b in chosen}
    new = [(u, v) for u, v in edges if (min(u, v), max(u, v)) not in drop]
    sa, sb = n, n + 1
    for a, b in chosen:
        new.append((sa, b))
        new.append((a, sb))
    return n + 2, new


def _bad(n, E, D):
    """Number of unordered vertex pairs at distance more than D (bitmask balls)."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(n, E, D, rng, t_end, T0=2.0, T1=0.1):
    """Degree-preserving 2-switch annealing that drives the bad-pair count to zero.

    A switch replaces (a1,b1),(a2,b2) by (a1,b2),(a2,b1), so the side-0 and
    side-1 degree sequences are unchanged. The temperature decays with elapsed time.
    """
    E = list(E)
    S = set(E)
    cur = _bad(n, E, D)
    t0 = time.monotonic()
    span = max(1e-6, t_end - t0)
    m = len(E)
    while cur > 0:
        now = time.monotonic()
        if now >= t_end:
            break
        T = T0 * (T1 / T0) ** ((now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        ne1 = (a1, b2)
        ne2 = (a2, b1)
        if ne1 in S or ne2 in S:
            continue
        E[i] = ne1
        E[j] = ne2
        c2 = _bad(n, E, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add(ne1)
            S.add(ne2)
            cur = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return cur, E


def _grow(best, d, D, bound, t_end, rng):
    """Repeatedly splice in two vertices and repair with annealing; keep only valid results."""
    cur = best
    while time.monotonic() < t_end and cur[0] < bound:
        n0, e0 = cur
        color, adj = _colour(n0, e0)
        sp = _splice(n0, e0, d, color, adj, rng)
        if sp is None:
            break
        n1, e1 = sp
        color1, _ = _colour(n1, e1)
        E = _orient(e1, color1)
        now = time.monotonic()
        remaining = t_end - now
        slice_end = min(t_end, now + max(1.0, 0.35 * remaining))
        cost, E2 = _anneal(n1, E, D, rng, slice_end)
        if cost == 0:
            e_new = list(E2)
            if lib.is_valid(n1, e_new, d, D):
                cur = (n1, e_new)
    return cur


def build(d, D, seed, time_limit):
    start = time.monotonic()
    t_end = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    cands = [lib.haar_graph(d, range(d))]  # K_{d,d}, diameter 2
    if D >= 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break

    best = None
    for n, e in cands:
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)
    if best is None:
        return 1, []

    if D >= 3 and d >= 3:
        bound = lib._moore_bound(d, D)
        if best[0] < bound:
            best = _grow(best, d, D, bound, t_end, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
