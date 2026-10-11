import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Regular bipartite graphs searched directly, grown one side at a time.
#
# A d-regular bipartite graph is stored as a list E of (a, b) pairs, with
# a in 0..s-1 (side A) and b in 0..s-1 (side B). Vertex ids are a and s+b.
#
# Growth: pick a matching of d edges (a_i, b_i), delete them, add a new A
# vertex x joined to every b_i and a new B vertex y joined to every a_i.
# This keeps the graph d-regular and bipartite and adds one vertex per side.
#
# Repair: simulated annealing over 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1),
# which preserve regularity and bipartiteness. The cost is the number of ordered
# vertex pairs at distance more than D.
# ----------------------------------------------------------------------------


def _cost(s, E, D):
    """Ordered pairs of vertices at distance > D in the bipartite graph given by E. Zero means valid."""
    n = 2 * s
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(s + b)
        adj[s + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _grow(s, E, d, rng):
    """Add one vertex per side by splitting a matching of d edges. Returns (s+1, E') or None."""
    order = E[:]
    rng.shuffle(order)
    used_a, used_b = set(), set()
    chosen = []
    for a, b in order:
        if a in used_a or b in used_b:
            continue
        chosen.append((a, b))
        used_a.add(a)
        used_b.add(b)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    chosen_set = set(chosen)
    newE = [e for e in E if e not in chosen_set]
    x = s  # new A vertex
    y = s  # new B vertex
    for a, b in chosen:
        newE.append((a, y))
        newE.append((x, b))
    return s + 1, newE


def _anneal(s, E, D, rng, deadline, iters):
    """Simulated annealing over 2-switches. Returns (cost, E); cost 0 means diameter <= D."""
    m = len(E)
    S = set(E)
    cost = _cost(s, E, D)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in S or e2 in S:
            continue
        E[i] = e1
        E[j] = e2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(e1)
        S.add(e2)
        c2 = _cost(s, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard(e1)
            S.discard(e2)
            S.add((a1, b1))
            S.add((a2, b2))
    return cost, E


# ----------------------------------------------------------------------------
# Projective plane base (cheap, D >= 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D} has diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main family: grow a d-regular bipartite graph one side at a time,
    # repairing diameter with annealing over 2-switches.
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    moore = lib.moore_bound(d, D)
    s = d
    E = [(a, b) for a in range(d) for b in range(d)]
    level_iters = 4000

    while time.monotonic() < deadline and 2 * (s + 1) <= moore:
        g = _grow(s, E, d, rng)
        if g is None:
            continue
        s2, E2 = g
        cost, E2 = _anneal(s2, E2, D, rng, deadline, level_iters)
        if cost == 0:
            s, E = s2, E2
            if 2 * s > best[0]:
                consider(2 * s, [(a, s + b) for a, b in E])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
