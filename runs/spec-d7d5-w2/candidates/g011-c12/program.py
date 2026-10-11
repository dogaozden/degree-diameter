import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New construction for the weak targets: edge-switch repair on general
# d-regular bipartite graphs.
#
# The parent searched bi-Cayley lifts with voltage moves. This version uses no
# group structure. It starts from K_{d,d} and repeatedly inserts pairs of
# vertices. Each insertion keeps the graph d-regular and bipartite. Then it
# anneals with degree-preserving edge switches (a1-b1, a2-b2 -> a1-b2, a2-b1)
# to drive the number of vertex pairs at distance > D to zero. A step is kept
# only when the cost reaches zero, so every accepted snapshot is a valid graph.
# The final graph is checked with lib.is_valid, and the safe fallback is used
# if that check fails.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _bad(adj, d, D):
    """Number of unordered vertex pairs at distance > D, via bit-packed reach sets."""
    n = len(adj)
    R = np.packbits(np.eye(n, dtype=bool), axis=1)
    nbr = np.array(adj, dtype=np.int64)
    for _ in range(D):
        new = R.copy()
        for l in range(d):
            new |= R[nbr[:, l]]
        if np.array_equal(new, R):
            break
        R = new
    total = int(_POP8[R].sum())
    return (n * n - total) // 2


def _switch(adj, a1, i1, a2, i2):
    """Swap the B-ends of slots i1 of a1 and i2 of a2. Applying it twice restores the graph."""
    b1 = adj[a1][i1]
    b2 = adj[a2][i2]
    j1 = adj[b1].index(a1)
    j2 = adj[b2].index(a2)
    adj[a1][i1] = b2
    adj[b2][j2] = a1
    adj[a2][i2] = b1
    adj[b1][j1] = a2


def _add_pair(adj, A, B, d, rng):
    """Add x (side A) and y (side B) with x~y. Remove d-1 matching edges and rewire them to x and y."""
    order = A[:]
    rng.shuffle(order)
    pairs = []
    used_b = set()
    for a in order:
        if len(pairs) == d - 1:
            break
        b = adj[a][rng.randrange(d)]
        if b in used_b:
            continue
        pairs.append((a, b))
        used_b.add(b)
    if len(pairs) < d - 1:
        return False
    x = len(adj)
    y = x + 1
    adj.append([])
    adj.append([])
    for a, b in pairs:
        adj[a][adj[a].index(b)] = y
        adj[b][adj[b].index(a)] = x
    adj[x] = [b for _, b in pairs] + [y]
    adj[y] = [a for a, _ in pairs] + [x]
    A.append(x)
    B.append(y)
    return True


def _repair(adj, d, D, A, B, rng, deadline, max_evals):
    """Simulated annealing over edge switches until no pair is farther than D apart."""
    T = 0.5
    cost = _bad(adj, d, D)
    evals = 0
    while cost > 0 and evals < max_evals and time.monotonic() < deadline:
        a1 = A[rng.randrange(len(A))]
        a2 = A[rng.randrange(len(A))]
        if a1 == a2:
            continue
        i1 = rng.randrange(d)
        i2 = rng.randrange(d)
        b1 = adj[a1][i1]
        b2 = adj[a2][i2]
        if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        _switch(adj, a1, i1, a2, i2)
        c2 = _bad(adj, d, D)
        evals += 1
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _switch(adj, a1, i1, a2, i2)
    return cost == 0


def _grow(d, D, seed, deadline):
    """Grow a d-regular bipartite graph from K_{d,d}. Return (n, edges) of the last repaired snapshot."""
    rng = random.Random(seed)
    adj = [list(range(d, 2 * d)) for _ in range(d)] + [list(range(d)) for _ in range(d)]
    A = list(range(d))
    B = list(range(d, 2 * d))
    snap = ([list(r) for r in adj], list(A), list(B))
    p, fails = 1, 0
    while time.monotonic() < deadline and fails < 6:
        ok = True
        for _ in range(p):
            if not _add_pair(adj, A, B, d, rng):
                ok = False
                break
        if ok:
            ok = _repair(adj, d, D, A, B, rng, deadline, 200)
        if ok:
            snap = ([list(r) for r in adj], list(A), list(B))
            fails = 0
            p = max(1, len(adj) // 50)
        else:
            adj[:] = [list(r) for r in snap[0]]
            A[:] = snap[1]
            B[:] = snap[2]
            fails += 1
            p = max(1, p // 2)
    sadj = snap[0]
    n = len(sadj)
    edges = [(u, v) for u in range(n) for v in sadj[u] if u < v]
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact incidence graph of PG(2, q) for D = 3 (calibration case d=3 gives 14).
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        if lib.is_prime_power(d - 1):
            return best

    # Main path: pair-insertion growth with edge-switch repair.
    if d >= 3:
        grown = _grow(d, D, seed, deadline)
        consider(*grown)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
