"""Grow-and-repair search for bipartite degree-d, diameter-D graphs.

Representation: every graph is d-regular and bipartite with equal sides.
A side-A vertex is local index a in 0..p-1 and a side-B vertex is local index b in 0..p-1
(global id p+b). Growth adds one vertex to each side by rewiring d edges, which keeps
every degree at d. Repair uses degree-preserving edge switches that minimise the number
of vertex pairs at distance > D. Every returned graph is checked with lib.is_valid.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bit-parallel bad-pair counter on adjacency lists.
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance more than D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _adj_from(p, E):
    adj = [[] for _ in range(2 * p)]
    for a, b in E:
        adj[a].append(p + b)
        adj[p + b].append(a)
    return adj


def _rep(lst, old, new):
    lst[lst.index(old)] = new


def _switch(adj, p, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1) in the adjacency lists."""
    B1, B2 = p + b1, p + b2
    _rep(adj[a1], B1, B2)
    _rep(adj[B1], a1, a2)
    _rep(adj[a2], B2, B1)
    _rep(adj[B2], a2, a1)


def _glob(p, E):
    return [(a, p + b) for a, b in E]


# ----------------------------------------------------------------------------
# Growth: add one A and one B vertex, taking d edges from the graph.
# ----------------------------------------------------------------------------

def _grow(p, E, d, rng):
    """Return (p+1, E') with every degree still d, or None if no suitable edges are found."""
    m = len(E)
    if d > m or d < 1:
        return None
    idxs = None
    for _ in range(300):
        cand = rng.sample(range(m), d)
        As = {E[i][0] for i in cand}
        Bs = {E[i][1] for i in cand}
        if len(As) == d and len(Bs) == d:
            idxs = cand
            break
    if idxs is None:
        return None
    E2 = list(E)
    for idx in idxs:
        a, b = E2[idx]
        E2[idx] = (p, b)       # new A vertex p joins b
        E2.append((a, p))      # a joins new B vertex p
    return p + 1, E2


# ----------------------------------------------------------------------------
# Repair: edge-switch annealing on the bad-pair count.
# ----------------------------------------------------------------------------

def _anneal(p, D, E, rng, deadline, iters, T0=2.0, T1=0.05):
    E = [tuple(e) for e in E]
    eset = set(E)
    adj = _adj_from(p, E)
    cost = _bad_pairs(2 * p, adj, D)
    m = len(E)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        _switch(adj, p, a1, b1, a2, b2)
        new = _bad_pairs(2 * p, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            E[i] = (a1, b2)
            E[j] = (a2, b1)
        else:
            _switch(adj, p, a1, b2, a2, b1)  # undo
    return E if cost == 0 else None


# ----------------------------------------------------------------------------
# Seeds.
# ----------------------------------------------------------------------------

def _haar_search(d, D, m, rng, deadline, iters):
    """Hill-climb a d-element connection set S in Z_m so that the Haar graph has diameter <= D."""
    if m < d:
        return None

    def cost(S):
        adj = [[] for _ in range(2 * m)]
        for i in range(m):
            for s in S:
                b = m + (i + s) % m
                adj[i].append(b)
                adj[b].append(i)
        return _bad_pairs(2 * m, adj, D)

    S = rng.sample(range(m), d)
    c = cost(S)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(d)
        cand = rng.randrange(m)
        if cand in S:
            continue
        T = list(S)
        T[idx] = cand
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _haar_seed(d, D, deadline, rng):
    """Return (m, S) for the largest Haar graph found, or None."""
    best = None
    m = d + 1
    fails = 0
    while time.monotonic() < deadline and fails < 2:
        S = _haar_search(d, D, m, rng, deadline, 150)
        if S is None:
            fails += 1
        else:
            best = (m, S)
            fails = 0
        m += 1
    return best


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_p = d
    best_E = [(a, b) for a in range(d) for b in range(d)]
    best_glob = _glob(d, best_E)

    def consider(p, E):
        nonlocal best_p, best_E, best_glob
        if p <= best_p:
            return
        glob = _glob(p, E)
        if lib.is_valid(2 * p, glob, d, D):
            best_p, best_E, best_glob = p, list(E), glob

    # Seeds: projective plane (diameter 3, d-regular when d-1 is a prime power), then Haar.
    seed_deadline = start + 0.25 * (deadline - start)
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        n2, edges = lib.projective_plane_incidence(d - 1)
        p = n2 // 2
        E = [(u, v - p) for u, v in edges]
        consider(p, E)
    hs = _haar_seed(d, D, seed_deadline, rng)
    if hs is not None:
        m, S = hs
        E = [(i, (i + s) % m) for i in range(m) for s in S]
        consider(m, E)

    # Main phase: repeatedly grow the current best by one vertex per side and repair.
    ITER = 3000
    while time.monotonic() < deadline:
        g = _grow(best_p, best_E, d, rng)
        if g is None:
            break
        p2, E2 = g
        res = _anneal(p2, D, E2, rng, deadline, ITER)
        if res is not None:
            consider(p2, res)

    if not lib.is_valid(2 * best_p, best_glob, d, D):
        return 2 * d, _glob(d, [(a, b) for a in range(d) for b in range(d)])
    return 2 * best_p, best_glob
