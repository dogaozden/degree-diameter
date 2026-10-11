import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# NEW helper: spliced vertex-pair insertion followed by bad-pair annealing.
#
# Insert a new A-vertex a* and a new B-vertex b* into a graph that is already
# valid. Take a matching of d edges (a_i, b_i), delete it, then add a*-b_i and
# a_i-b*. Old degrees are unchanged, and a*, b* reach degree d. The graph has
# two more vertices and is generally not of diameter D yet.
#
# Repair: double-edge swaps (a,b),(c,e) -> (a,e),(c,b) keep every degree and
# the bipartition. Simulated annealing minimises the number of vertex pairs at
# distance > D, computed with a numpy reachability matrix.
# ----------------------------------------------------------------------------

def _sides(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    return color


def _oriented(n, E):
    """Return edges oriented so the first endpoint lies on side 0."""
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    color = _sides(n, adj)
    return [[u, v] if color[u] == 0 else [v, u] for u, v in E]


def _cost(A, D):
    """Unordered number of vertex pairs at distance > D (A is a symmetric 0/1 float32 matrix)."""
    n = A.shape[0]
    M = A + np.eye(n, dtype=np.float32)
    R = M
    for _ in range(D - 1):
        R = np.minimum(R @ M, 1.0)
    return int(n * n - np.count_nonzero(R)) // 2


def _splice(n, E, d, rng):
    """Insert new vertices a* = n (side 0) and b* = n+1 (side 1) by splicing a d-matching."""
    idx = list(range(len(E)))
    rng.shuffle(idx)
    used_a, used_b, pick = set(), set(), []
    for i in idx:
        a, b = E[i]
        if a in used_a or b in used_b:
            continue
        pick.append(i)
        used_a.add(a)
        used_b.add(b)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    pickset = set(pick)
    newE = [e for k, e in enumerate(E) if k not in pickset]
    newE += [[n, E[i][1]] for i in pick]
    newE += [[E[i][0], n + 1] for i in pick]
    return n + 2, newE


def _anneal(n, E, D, rng, deadline):
    """Double-edge-swap annealing on bad pairs. Returns (success, E)."""
    A = np.zeros((n, n), dtype=np.float32)
    for a, b in E:
        A[a, b] = 1.0
        A[b, a] = 1.0
    cost = _cost(A, D)
    m = len(E)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 0.6 * (0.05 / 0.6) ** min(1.0, (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or A[a, e] or A[c, b]:
            continue
        A[a, b] = A[b, a] = 0.0
        A[c, e] = A[e, c] = 0.0
        A[a, e] = A[e, a] = 1.0
        A[c, b] = A[b, c] = 1.0
        new = _cost(A, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            E[i] = [a, e]
            E[j] = [c, b]
        else:
            A[a, e] = A[e, a] = 0.0
            A[c, b] = A[b, c] = 0.0
            A[a, b] = A[b, a] = 1.0
            A[c, e] = A[e, c] = 1.0
    return cost == 0, E


def _grow_repair(n, E, d, D, deadline, rng):
    """Repeat splice-and-anneal attempts with fresh matchings until one succeeds or time runs out."""
    while time.monotonic() < deadline:
        now = time.monotonic()
        budget = min(deadline, now + max(3.0, 0.2 * (deadline - now)))
        sp = _splice(n, [list(e) for e in E], d, rng)
        if sp is None:
            return None
        n2, E2 = sp
        ok, E3 = _anneal(n2, E2, D, rng, budget)
        if ok:
            return n2, E3
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for cand in (_ara(d), _best_pg(d)):
            if cand is not None:
                consider(cand[0], cand[1])

        # New stage: grow the best diameter-3 graph by splice-and-repair, two vertices at a time.
        moore = lib._moore_bound(d, D)
        if d >= 3 and best_n < moore:
            cur_n, cur_E = best_n, _oriented(best_n, best[1])
            while cur_n + 2 <= moore and time.monotonic() < deadline:
                res = _grow_repair(cur_n, cur_E, d, D, deadline, rng)
                if res is None:
                    break
                cur_n, cur_E = res
                consider(cur_n, [(int(a), int(b)) for a, b in cur_E])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], [(int(u), int(v)) for u, v in best[1]]
