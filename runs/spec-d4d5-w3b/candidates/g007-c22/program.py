import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Graph helpers on plain adjacency lists.
# ----------------------------------------------------------------------------

def _adj(n, E):
    """Adjacency lists for a bipartite edge list E of [left, right] pairs."""
    adj = [[] for _ in range(n)]
    for l, r in E:
        adj[l].append(r)
        adj[r].append(l)
    return adj


def _color(n, adj):
    """Two-colouring by DFS; returns a list of 0/1 labels."""
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


def _bad(n, adj, D):
    """Ordered count of vertex pairs at distance > D. Zero means diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _apply(E, S, deg, changes):
    """Replace E[i] by new edges given as (i, new_left, new_right); return the old values for undo."""
    olds = []
    for i, _nl, _nr in changes:
        ol, orr = E[i]
        S.discard((ol, orr))
        deg[ol] -= 1
        deg[orr] -= 1
        olds.append((i, ol, orr))
    for i, nl, nr in changes:
        E[i] = [nl, nr]
        S.add((nl, nr))
        deg[nl] += 1
        deg[nr] += 1
    return olds


# ----------------------------------------------------------------------------
# Edge-switch simulated annealing on a fixed-order balanced bipartite graph.
#
# State: a bipartite graph with max degree d on n vertices (colour 0 = left,
# colour 1 = right). Cost = ordered number of pairs at distance > D.
# Moves: 2-switch (keeps degrees), slide (moves one edge endpoint onto a
# deficient vertex), and add (joins two deficient vertices; always helpful).
# ----------------------------------------------------------------------------

def _sa_level(n, col, E, d, D, deadline, rng):
    """Anneal edges E (in place) until diameter <= D; return E on success, else None."""
    deg = [0] * n
    S = set()
    for l, r in E:
        deg[l] += 1
        deg[r] += 1
        S.add((l, r))
    if max(deg, default=0) > d:
        return None
    lefts = [v for v in range(n) if col[v] == 0]
    rights = [v for v in range(n) if col[v] == 1]
    cost = _bad(n, _adj(n, E), D)

    T0, T1 = 3.0, 0.1
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline or not E:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        r = rng.random()

        if r < 0.1:
            defl = [a for a in lefts if deg[a] < d]
            defr = [b for b in rights if deg[b] < d]
            if not defl or not defr:
                continue
            a = rng.choice(defl)
            b = rng.choice(defr)
            if (a, b) in S:
                continue
            E.append([a, b])
            S.add((a, b))
            deg[a] += 1
            deg[b] += 1
            cost = _bad(n, _adj(n, E), D)
            continue

        if r < 0.5:
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2 or (a1, b2) in S or (a2, b1) in S:
                continue
            changes = [(i, a1, b2), (j, a2, b1)]
        elif r < 0.75:
            defl = [a for a in lefts if deg[a] < d]
            if not defl:
                continue
            a = rng.choice(defl)
            i = rng.randrange(len(E))
            x, y = E[i]
            if x == a or (a, y) in S:
                continue
            changes = [(i, a, y)]
        else:
            defr = [b for b in rights if deg[b] < d]
            if not defr:
                continue
            b = rng.choice(defr)
            i = rng.randrange(len(E))
            x, y = E[i]
            if y == b or (x, b) in S:
                continue
            changes = [(i, x, b)]

        olds = _apply(E, S, deg, changes)
        new_cost = _bad(n, _adj(n, E), D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
        else:
            _apply(E, S, deg, olds)

    if cost == 0:
        return E
    return None


# ----------------------------------------------------------------------------
# Build: grow a valid graph by two vertices (one per side) at a time, each
# step repaired by annealing. Every accepted graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Plain projective plane incidence graph (diameter 3) as a starting point.
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n_pg, e_pg = lib.projective_plane_incidence(q)
                consider(n_pg, e_pg)
                break

    n0, e0 = best
    col0 = _color(n0, _adj(n0, e0))
    E0 = [[u, v] if col0[u] == 0 else [v, u] for u, v in e0]

    cur_n, cur_col, cur_E = n0, col0, E0
    while time.monotonic() < end:
        remaining = end - time.monotonic()
        budget = min(remaining, max(1.0, remaining / 5.0))
        n1 = cur_n + 2
        col1 = cur_col + [0, 1]
        E1 = [list(e) for e in cur_E]
        res = _sa_level(n1, col1, E1, d, D, time.monotonic() + budget, rng)
        if res is None:
            continue
        edges = [(l, r) for l, r in res]
        if lib.is_valid(n1, edges, d, D):
            cur_n, cur_col, cur_E = n1, col1, res
            consider(n1, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best[0], list(best[1])
