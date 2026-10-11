"""Bipartite diameter-D graph builder.

New in this version: degree-preserving growth by edge-split vertex insertion,
followed by simulated annealing with double-edge switches. Every intermediate
state is a d-regular bipartite graph. The cost is the number of vertex pairs
at distance more than D, computed with Python big-int bitsets. Growth starts
from K_{d,d} and adds one vertex per side at a time. Each size is accepted
only once the annealer drives the cost to zero.

Projective-plane and Araujo-Pardo-Lopez constructions are kept as cheap
baselines for D = 3. Every candidate is checked with lib.is_valid before it
is returned, and K_{d,d} is the fallback.
"""
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bipartite d-regular state: side size M, edges E = list of (a, b) meaning
# A-vertex a joined to B-vertex M + b. Vertices: A = 0..M-1, B = M..2M-1.
# ----------------------------------------------------------------------------

def _cost(M, E, D):
    """Number of unordered vertex pairs at distance > D (0 means valid)."""
    n = 2 * M
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(M + b)
        adj[M + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _insert(M, E, d, rng):
    """Edge-split insertion of one new A vertex M and one new B vertex M.

    Pick d edges (a_i, b_i) with distinct a_i and distinct b_i. Replace each by
    (a_i, M) and (M, b_i). Every old vertex keeps its degree, and the two new
    vertices get degree d. Returns (M + 1, new_edges), or None.
    """
    order = list(range(len(E)))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    drop = set(chosen)
    newE = [E[i] for i in range(len(E)) if i not in drop]
    for idx in chosen:
        a, b = E[idx]
        newE.append((a, M))
        newE.append((M, b))
    return M + 1, newE


def _anneal(M, E, D, rng, deadline, cap, T=0.5):
    """Simulated annealing with double-edge switches on the bipartite edge list.

    A switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keeps every degree and the
    bipartition. Returns (0, E) on success, else (best_cost, best_E).
    """
    E = list(E)
    S = set(E)
    cost = _cost(M, E, D)
    best_cost, best_E = cost, list(E)
    m_e = len(E)
    for _ in range(cap):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(m_e)
        j = rng.randrange(m_e)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        p = (a1, b2)
        q = (a2, b1)
        if p in S or q in S:
            continue
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(p)
        S.add(q)
        E[i] = p
        E[j] = q
        c2 = _cost(M, E, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_E = list(E)
        else:
            S.discard(p)
            S.discard(q)
            S.add((a1, b1))
            S.add((a2, b2))
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    if cost == 0:
        return 0, E
    return best_cost, best_E


def _grow_search(d, D, rng, deadline):
    """Grow a valid d-regular bipartite graph one vertex pair at a time.

    Starts from K_{d,d}. Each step inserts a vertex pair, then anneals the
    cost to zero. A failed step retries from the last valid state with fresh
    randomness, up to a limited number of failures in a row.
    Returns (M, E) for the largest valid side size found.
    """
    base_M = d
    base_E = [(a, b) for a in range(d) for b in range(d)]
    best = (base_M, list(base_E))
    fails = 0
    while time.monotonic() < deadline and fails < 6:
        ins = _insert(base_M, base_E, d, rng)
        if ins is None:
            break
        M, E = ins
        cap = 300 + 3 * M + 150 * fails
        cost, Eo = _anneal(M, E, D, rng, deadline, cap)
        if cost == 0:
            base_M, base_E = M, list(Eo)
            best = (M, list(Eo))
            fails = 0
        else:
            fails += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    base = lib.haar_graph(d, range(d))

    cands = [base]
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            cands.append(pg)
        ar = _araujo(d)
        if ar is not None:
            cands.append(ar)
    if D >= 4 and d >= 3:
        rng = random.Random(seed * 1000003 + d * 101 + D)
        M, E = _grow_search(d, D, rng, deadline)
        cands.append((2 * M, [(a, M + b) for a, b in E]))

    cands.sort(key=lambda c: -c[0])
    for n, e in cands:
        if lib.is_valid(n, e, d, D):
            return n, e
    return base
