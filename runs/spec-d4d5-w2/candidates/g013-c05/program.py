import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy: grow d-regular bipartite graphs one vertex per side at a time.
#
# Every graph here is d-regular and bipartite on sides of size s (vertices
# A_i = i and B_j = s + j). A growth step inserts a new A vertex and a new B
# vertex by subdividing d-1 disjoint edges, which keeps every old degree
# unchanged. Simulated annealing with double-edge swaps (which also preserve
# degrees and bipartiteness) then drives the number of unreachable or
# too-far pairs to zero. A candidate is accepted only if its cost is exactly
# zero, so each accepted state has diameter <= D.
# ----------------------------------------------------------------------------


def _cost(s, eds, D):
    """Number of unordered vertex pairs at distance > D (or disconnected)."""
    N = 2 * s
    nb = [[] for _ in range(N)]
    for i, j in eds:
        b = s + j
        nb[i].append(b)
        nb[b].append(i)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in nb[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return sum(N - x.bit_count() for x in reach) // 2


def _grow(s, d, eds, rng):
    """Insert a new A vertex (index s) and a new B vertex (index s) with degree d.

    Pick d-1 edges (i, j) with distinct endpoints; replace each by (a, j) and
    (i, b), then add (a, b). Old degrees are unchanged, and new vertices get degree d.
    Returns (s+1, edges) or None if not enough disjoint edges exist.
    """
    a = s
    b = s
    out = list(eds)
    order = list(range(len(out)))
    rng.shuffle(order)
    used_i, used_j, chosen = set(), set(), []
    for idx in order:
        if len(chosen) == d - 1:
            break
        i, j = out[idx]
        if i in used_i or j in used_j:
            continue
        used_i.add(i)
        used_j.add(j)
        chosen.append(idx)
    if len(chosen) < d - 1:
        return None
    removed = set(chosen)
    new_edges = [e for k, e in enumerate(out) if k not in removed]
    for idx in chosen:
        i, j = out[idx]
        new_edges.append((a, j))
        new_edges.append((i, b))
    new_edges.append((a, b))
    return s + 1, new_edges


def _anneal(s, D, eds, rng, deadline):
    """Annealed double-edge swaps on the list `eds` (modified in place).

    Returns True as soon as the cost reaches zero (eds is then valid),
    or False at the deadline (eds is then left in an arbitrary state).
    """
    eset = set(eds)
    cur = _cost(s, eds, D)
    if cur == 0:
        return True
    E = len(eds)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 3.0, 0.2
    T = T0
    it = 0
    while True:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                return False
            frac = min(1.0, (now - t0) / span)
            T = T0 * (T1 / T0) ** frac

        x = rng.randrange(E)
        y = rng.randrange(E)
        if x == y:
            continue
        a1, b1 = eds[x]
        a2, b2 = eds[y]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue

        eds[x] = (a1, b2)
        eds[y] = (a2, b1)
        new = _cost(s, eds, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            if cur == 0:
                return True
        else:
            eds[x] = (a1, b1)
            eds[y] = (a2, b2)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    K_edges = [(i, d + j) for i in range(d) for j in range(d)]
    if D == 2:
        return 2 * d, K_edges  # K_{d,d} is Moore-optimal for D = 2

    # D = 3 with d - 1 a prime power: the projective plane incidence graph is Moore-optimal.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    bound = lib.moore_bound(d, D)
    best_s = d
    best_eds = [(i, j) for i in range(d) for j in range(d)]
    s, eds = best_s, list(best_eds)

    # Grow one vertex per side while the annealer can close the gap.
    while True:
        now = time.monotonic()
        if now >= deadline or 2 * (s + 1) > bound:
            break
        cand = _grow(s, d, eds, rng)
        if cand is None:
            break
        ns, ce = cand
        rem = deadline - now
        ok = _anneal(ns, D, ce, rng, now + 0.5 * rem)
        if ok:
            s, eds = ns, ce
            best_s, best_eds = s, list(eds)

    n = 2 * best_s
    edges = [(i, best_s + j) for i, j in best_eds]
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return 2 * d, K_edges
