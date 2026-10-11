import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Different construction from the parent: a d-regular bipartite graph on 2m
# vertices, grown one vertex per side at a time. Each growth step adds a new
# A-vertex and a new B-vertex by splicing them into d edges of the current
# graph, which keeps every degree at d. Then a double-edge-swap annealer
# drives the number of ordered pairs at distance > D to zero. Only zero-cost
# states are kept as snapshots, and every snapshot is checked with lib.is_valid.
# ----------------------------------------------------------------------------

_POP = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _build_struct(m, E):
    """Adjacency lists and a boolean incidence matrix for side-0 index a, side-1 index b."""
    nbr0 = [[] for _ in range(m)]
    nbr1 = [[] for _ in range(m)]
    M = np.zeros((m, m), dtype=bool)
    for a, b in E:
        nbr0[a].append(b)
        nbr1[b].append(a)
        M[a, b] = True
    return [tuple(e) for e in E], nbr0, nbr1, M


def _cost(m, d, D, nbr0, nbr1):
    """Ordered pairs (u, v) with distance > D. Zero means connected with diameter <= D."""
    n = 2 * m
    N_all = np.empty((n, d), dtype=np.int64)
    N_all[:m] = np.array(nbr0, dtype=np.int64) + m
    N_all[m:] = np.array(nbr1, dtype=np.int64)
    R = np.packbits(np.eye(n, dtype=bool), axis=1)
    for _ in range(D):
        R2 = R | np.bitwise_or.reduce(R[N_all], axis=1)
        if np.array_equal(R2, R):
            break
        R = R2
    ones = int(_POP[R].sum())
    return n * n - ones


def _apply_swap(i, j, E, nbr0, nbr1, M):
    """Double-edge swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Self-inverse when called on the new indices."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    E[i] = (a1, b2)
    E[j] = (a2, b1)
    M[a1, b1] = False
    M[a2, b2] = False
    M[a1, b2] = True
    M[a2, b1] = True
    nbr0[a1][nbr0[a1].index(b1)] = b2
    nbr0[a2][nbr0[a2].index(b2)] = b1
    nbr1[b1][nbr1[b1].index(a1)] = a2
    nbr1[b2][nbr1[b2].index(a2)] = a1


def _anneal(m, d, D, E, nbr0, nbr1, M, rng, deadline, T=2.0):
    """Metropolis annealing over double-edge swaps. Returns the final cost (0 means success)."""
    cost = _cost(m, d, D, nbr0, nbr1)
    while cost and time.monotonic() < deadline:
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or M[a1, b2] or M[a2, b1]:
            continue
        _apply_swap(i, j, E, nbr0, nbr1, M)
        new = _cost(m, d, D, nbr0, nbr1)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            _apply_swap(i, j, E, nbr0, nbr1, M)  # inverse move restores the old state
    return cost


def _grow(m, E, d, rng):
    """Add one A-vertex m and one B-vertex m. Pick d edges (x_i, y_i) with distinct ends,
    replace them by (m, y_i) and (x_i, m). All degrees stay d. Returns (m+1, edges) or None."""
    chosen = None
    for _ in range(200):
        order = list(range(len(E)))
        rng.shuffle(order)
        ua, ub, pick = set(), set(), []
        for idx in order:
            a, b = E[idx]
            if a in ua or b in ub:
                continue
            ua.add(a)
            ub.add(b)
            pick.append(idx)
            if len(pick) == d:
                break
        if len(pick) == d:
            chosen = pick
            break
    if chosen is None:
        return None
    cs = set(chosen)
    newE = [E[i] for i in range(len(E)) if i not in cs]
    for idx in chosen:
        x, y = E[idx]
        newE.append((m, y))
        newE.append((x, m))
    return m + 1, newE


def _to_graph(m, E):
    """Convert side-0/side-1 indices to a single labelling: A vertices 0..m-1, B vertices m..2m-1."""
    return 2 * m, [(a, m + b) for a, b in E]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid whenever D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D <= 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # D = 3: projective plane incidence graph when d - 1 is a prime power.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)

    # Main search: grow an annealed d-regular bipartite graph.
    m = d
    E, nbr0, nbr1, M = _build_struct(m, [(a, b) for a in range(d) for b in range(d)])
    while time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        step_deadline = now + max(1.0, 0.5 * remaining)
        cost = _anneal(m, d, D, E, nbr0, nbr1, M, rng, min(step_deadline, deadline))
        if cost != 0:
            # Give this size the rest of the budget before giving up.
            cost = _anneal(m, d, D, E, nbr0, nbr1, M, rng, deadline)
            if cost != 0:
                break
        n, e = _to_graph(m, E)
        consider(n, e)
        grown = _grow(m, E, d, rng)
        if grown is None:
            break
        m, E = grown
        E, nbr0, nbr1, M = _build_struct(m, E)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
