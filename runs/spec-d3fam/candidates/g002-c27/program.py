import math
import random
import time

import lib


def _bipartition(n, adj):
    """Two-colouring of a graph given by adjacency lists; None if not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _best_base(d, D):
    """Largest valid fallback graph among several known constructions."""
    cands = [lib.haar_graph(d, range(d))]  # K_{d,d}, diameter 2
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    best = None
    for n, e in cands:
        try:
            if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
                best = (n, e)
        except Exception:
            pass
    return best


def _saturate(A, B, nb, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    defA = [a for a in A if len(nb[a]) < d]
    defB = [b for b in B if len(nb[b]) < d]
    pairs = [(a, b) for a in defA for b in defB if b not in nb[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(nb[a]) < d and len(nb[b]) < d and b not in nb[a]:
            nb[a].add(b)
            nb[b].add(a)


def _grow_pair(n, nb, color, d, rng):
    """Add one A-vertex x and one B-vertex y, both of degree d, by stealing edges.

    Returns (n+2, nb, color) with max degree <= d and bipartite, or None.
    """
    x, y = n, n + 1
    nb = nb + [set(), set()]
    color = color + [0, 1]
    total = n + 2
    A = [v for v in range(total) if color[v] == 0]
    B = [v for v in range(total) if color[v] == 1]
    _saturate(A, B, nb, d, rng)
    old_edges = [(a, b) for a in range(n) if color[a] == 0 for b in nb[a] if b < n]
    rng.shuffle(old_edges)
    for a, b in old_edges:
        if len(nb[x]) >= d and len(nb[y]) >= d:
            break
        if len(nb[x]) < d and len(nb[y]) < d and a not in nb[x] and b not in nb[y]:
            nb[a].discard(b)
            nb[b].discard(a)
            nb[a].add(x)
            nb[x].add(a)
            nb[b].add(y)
            nb[y].add(b)
    if len(nb[x]) < d or len(nb[y]) < d:
        return None
    return total, nb, color


def _cost(n, nb, D):
    """Number of unordered pairs at distance > D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(n, nb, color, D, rng, deadline, iters):
    """Threshold-accepting search over degree-preserving double edge swaps.

    Returns the edge list (a, b) with a on side 0 if cost reaches zero, else None.
    """
    E = [(a, b) for a in range(n) if color[a] == 0 for b in nb[a]]
    eset = set(E)
    cost = _cost(n, nb, D)
    if cost == 0:
        return E
    for it in range(iters):
        if time.monotonic() > deadline:
            break
        T = 1.0 * (0.02 ** (it / iters))
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        nb[a1].discard(b1)
        nb[b1].discard(a1)
        nb[a2].discard(b2)
        nb[b2].discard(a2)
        nb[a1].add(b2)
        nb[b2].add(a1)
        nb[a2].add(b1)
        nb[b1].add(a2)
        c2 = _cost(n, nb, D)
        u = 1.0 - rng.random()
        if c2 <= cost - T * math.log(u):
            cost = c2
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            if cost == 0:
                return E
        else:
            nb[a1].discard(b2)
            nb[b2].discard(a1)
            nb[a2].discard(b1)
            nb[b1].discard(a2)
            nb[a1].add(b1)
            nb[b1].add(a1)
            nb[a2].add(b2)
            nb[b2].add(a2)
    return E if cost == 0 else None


def _improve(best, d, D, deadline, rng):
    """Repeatedly try to grow the best valid graph by two vertices."""
    bound = lib._moore_bound(d, D)
    misses = 0
    while time.monotonic() < deadline:
        n, edges = best
        if n + 2 > bound:
            break
        nb = [set() for _ in range(n)]
        for u, v in edges:
            nb[u].add(v)
            nb[v].add(u)
        color = _bipartition(n, [list(s) for s in nb])
        if color is None:
            break
        g = _grow_pair(n, nb, color, d, rng)
        if g is None:
            misses += 1
            if misses > 50:
                break
            continue
        n2, nb2, c2 = g
        E = _anneal(n2, nb2, c2, D, rng, deadline, iters=4000)
        if E is not None:
            cand = [(int(a), int(b)) for a, b in E]
            if lib.is_valid(n2, cand, d, D):
                best = (n2, cand)
                misses = 0
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, time_limit - 5.0)
    if budget < 0.5:
        budget = 0.5 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _best_base(d, D)
    if best is None:
        best = lib.haar_graph(d, range(d))

    if D >= 3:
        try:
            best = _improve(best, d, D, deadline, rng)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
