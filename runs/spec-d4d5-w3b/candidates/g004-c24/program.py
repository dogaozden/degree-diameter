import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Degree-preserving edge-switch search on bipartite graphs.
#
# State: a d-regular bipartite graph stored as an edge list E of pairs (a, b),
# with a on the "A" side and b on the "B" side, plus adjacency sets over the
# shared vertex id space. Vertices are grown by a regularity-preserving insertion
# (two new vertices x in A and y in B), and the cost is the number of unordered
# vertex pairs at distance more than D. Simulated annealing with double-edge
# swaps (which keep every degree fixed) drives the cost to zero.
# ----------------------------------------------------------------------------


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
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


def _state_from_E(n, E):
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    return {"n": n, "E": [list(e) for e in E], "adj": adj}


def _insert(st, d, rng):
    """Add two vertices x (side A) and y (side B) using a size-d matching.

    Matching edges (a_i, b_i) are replaced by x-b_i and a_i-y. Every degree is
    preserved, so the graph stays d-regular and bipartite.
    """
    E = st["E"]
    adj = st["adj"]
    n = st["n"]
    pick = None
    for _ in range(60):
        order = list(range(len(E)))
        rng.shuffle(order)
        used_a, used_b, cur = set(), set(), []
        for idx in order:
            a, b = E[idx]
            if a in used_a or b in used_b:
                continue
            used_a.add(a)
            used_b.add(b)
            cur.append(idx)
            if len(cur) == d:
                break
        if len(cur) == d:
            pick = cur
            break
    if pick is None:
        return False
    x, y = n, n + 1
    adj.append(set())
    adj.append(set())
    old = [tuple(E[idx]) for idx in pick]
    for k, idx in enumerate(pick):
        a, b = old[k]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[x].add(b)
        adj[b].add(x)
        adj[y].add(a)
        adj[a].add(y)
        E[idx] = [x, b]
        E.append([a, y])
    st["n"] = n + 2
    return True


def _anneal(st, D, deadline, iters, rng):
    """Anneal double-edge swaps to minimise bad pairs. Returns the final cost."""
    E = st["E"]
    adj = st["adj"]
    n = st["n"]
    cost = _bad(n, adj, D)
    T = 0.5
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        m = len(E)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        # Apply (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
        adj[a1].discard(b1)
        adj[b1].discard(a1)
        adj[a2].discard(b2)
        adj[b2].discard(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            # Revert.
            adj[a1].discard(b2)
            adj[b2].discard(a1)
            adj[a2].discard(b1)
            adj[b1].discard(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)
            E[i] = [a1, b1]
            E[j] = [a2, b2]
    return cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 4.0)
    rng = random.Random(seed * 1000003 + d * 101 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Fallback and starting point: K_{d,d}, diameter 2 (valid for D >= 2).
    def complete_bipartite():
        return 2 * d, [(a, d + b) for a in range(d) for b in range(d)]

    if D == 2:
        return complete_bipartite()

    # Moore-optimal fast path for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Grow a d-regular bipartite graph from K_{d,d}, keeping the best valid one.
    best_n = 2 * d
    best_E = [(a, d + b) for a in range(d) for b in range(d)]
    fails = 0
    base_iters = 200

    while time.monotonic() < deadline:
        st = _state_from_E(best_n, best_E)
        if not _insert(st, d, rng):
            break
        iters = base_iters * (2 ** min(fails, 5))
        c = _anneal(st, D, deadline, iters, rng)
        if c == 0:
            best_n = st["n"]
            best_E = [tuple(e) for e in st["E"]]
            fails = 0
        else:
            fails += 1

    edges = [(int(a), int(b)) for a, b in best_E]
    if lib.is_valid(best_n, edges, d, D):
        return best_n, edges
    return complete_bipartite()
