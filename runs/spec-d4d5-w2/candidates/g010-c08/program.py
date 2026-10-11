import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New family: bipartite graphs with every vertex of degree exactly d, grown by
# vertex insertion and repaired by simulated annealing over edge swaps.
#
# Layout for a graph with h vertices per side: left i -> vertex i,
# right j -> vertex h + j. Edges are stored as local pairs [i, j].
#
# Insertion (h -> h+1): pick d edges (i_k, j_k) with distinct i's and distinct
# j's, delete them, add a new left x = h joined to all j_k and a new right
# y = h joined to all i_k. Every degree stays d, and the graph stays bipartite.
#
# Annealing: double edge swaps (a,b),(c,e) -> (a,e),(c,b) keep all degrees.
# The cost is the number of unordered pairs at distance > D, computed with
# boolean matrix powers of (I + A).
# ----------------------------------------------------------------------------


def _build_A(h, edges):
    """Float32 adjacency matrix of the bipartite graph on 2h vertices."""
    n = 2 * h
    A = np.zeros((n, n), dtype=np.float32)
    for i, j in edges:
        A[i, h + j] = 1.0
        A[h + j, i] = 1.0
    return A


def _cost(A, n, D):
    """Number of unordered vertex pairs at distance greater than D."""
    M = A.copy()
    np.fill_diagonal(M, np.float32(1.0))  # M = I + A
    one = np.float32(1.0)
    P = M
    for _ in range(D - 1):
        P = np.minimum(P @ M, one)
    nnz = int(np.count_nonzero(P))
    return (n * n - nnz) // 2


def _anneal(h, D, edges, rng, deadline):
    """Anneal edge swaps until the diameter is <= D. Returns True on success.

    `edges` is modified in place and holds a valid graph on success.
    """
    n = 2 * h
    m = len(edges)
    if m < 2:
        return False
    A = _build_A(h, edges)
    cost = _cost(A, n, D)
    it = 0
    T_HI, T_LO, PERIOD = 1.0, 0.05, 1500
    while cost > 0:
        if time.monotonic() >= deadline:
            return False
        it += 1
        phase = (it % PERIOD) / PERIOD
        T = T_LO + (T_HI - T_LO) * 0.5 * (1.0 + math.cos(math.pi * phase))

        p = rng.randrange(m)
        q = rng.randrange(m)
        if p == q:
            continue
        a, b = edges[p]
        c, e = edges[q]
        if a == c or b == e:
            continue
        if A[a, h + e] != 0 or A[c, h + b] != 0:
            continue

        # Apply swap: remove (a,b),(c,e); add (a,e),(c,b).
        A[a, h + b] = 0.0
        A[h + b, a] = 0.0
        A[c, h + e] = 0.0
        A[h + e, c] = 0.0
        A[a, h + e] = 1.0
        A[h + e, a] = 1.0
        A[c, h + b] = 1.0
        A[h + b, c] = 1.0

        new_cost = _cost(A, n, D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
            edges[p] = [a, e]
            edges[q] = [c, b]
        else:
            # Revert swap.
            A[a, h + e] = 0.0
            A[h + e, a] = 0.0
            A[c, h + b] = 0.0
            A[h + b, c] = 0.0
            A[a, h + b] = 1.0
            A[h + b, a] = 1.0
            A[c, h + e] = 1.0
            A[h + e, c] = 1.0
    return True


def _insert(h, d, edges, rng):
    """Vertex insertion: return (h+1, new_edges), or None if no suitable d edges exist."""
    idx = list(range(len(edges)))
    rng.shuffle(idx)
    chosen = []
    used_l = set()
    used_r = set()
    for k in idx:
        i, j = edges[k]
        if i in used_l or j in used_r:
            continue
        chosen.append(k)
        used_l.add(i)
        used_r.add(j)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    chosen_set = set(chosen)
    new_edges = [e for k, e in enumerate(edges) if k not in chosen_set]
    x = h  # new left vertex
    y = h  # new right vertex
    for k in chosen:
        i, j = edges[k]
        new_edges.append([x, j])
        new_edges.append([i, y])
    return h + 1, new_edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    # Fast path: the projective plane meets the Moore bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        cand = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(cand[0], cand[1], d, D):
            return cand

    if d < 2:
        return best

    budget = min(0.85 * time_limit, time_limit - 5.0)
    budget = max(budget, 0.5 * time_limit)
    deadline = start + budget

    moore = lib.moore_bound(d, D)
    h = d
    edges = [[i, j] for i in range(d) for j in range(d)]  # K_{d,d}

    while time.monotonic() < deadline:
        ok = _anneal(h, D, edges, rng, deadline)
        if not ok:
            break
        n = 2 * h
        cand_edges = [(i, h + j) for i, j in edges]
        if n > best[0] and lib.is_valid(n, cand_edges, d, D):
            best = (n, cand_edges)
        if 2 * (h + 1) > moore:
            break
        res = _insert(h, d, edges, rng)
        if res is None:
            break
        h, edges = res

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
