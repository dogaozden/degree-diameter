import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bold change: instead of hill-climbing a single connection set with a
# plateau walk, run a tabu search over bi-Cayley connection sets on
# semidirect groups Z_m x|_r Z_k. Distances are computed with vectorised
# numpy BFS from both sides, and the search sweeps group orders N just above
# the current record half-order. Every accepted graph is re-checked with
# lib.is_valid, and a K_{d,d} fallback is always available.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10      # groups tried per order N before moving on
TABU_ITERS = 260     # tabu steps per group
SAMPLE = 14          # random single-coordinate moves evaluated per step
TABU_LEN = 6         # steps a changed coordinate stays frozen
ORDER_WINDOW = 36    # sweep window for group order N above the lower bound


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Return (order, T, invs) with T[x, g] = x*g and invs[g] = g^-1 as numpy arrays."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(order)] for x in range(order)], dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    return order, T, invs


def _cost(N, T, invs, Sarr, D):
    """Number of (source, vertex) pairs not within distance D, from A_0 and from B_0.

    Bi-Cayley graph: A_x ~ B_{x s} for s in S. Left translation is an automorphism,
    so the two sources suffice.
    """
    Sinv = invs[Sarr]
    total = 0
    for from_a in (True, False):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if from_a:
            seenA[0] = True
            fa = np.array([0], dtype=np.int64)
            fb = np.empty(0, dtype=np.int64)
        else:
            seenB[0] = True
            fa = np.empty(0, dtype=np.int64)
            fb = np.array([0], dtype=np.int64)
        for _ in range(D):
            if fa.size == 0 and fb.size == 0:
                break
            nb = T[fa][:, Sarr].ravel()
            na = T[fb][:, Sinv].ravel()
            nb = np.unique(nb[~seenB[nb]])
            na = np.unique(na[~seenA[na]])
            seenB[nb] = True
            seenA[na] = True
            fa, fb = na, nb
        total += 2 * N - int(seenA.sum() + seenB.sum())
    return total


def _tabu(N, T, invs, d, D, rng, deadline, iters):
    """Tabu search for a connection set S (identity fixed WLOG) with zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(N, T, invs, np.array(S, dtype=np.int64), D)
    best_cost, best_S = cur, list(S)
    tabu_until = {}
    for it in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        move, move_val = None, None
        for _ in range(SAMPLE):
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in S:
                continue
            S2 = S[:]
            S2[i] = c
            v = _cost(N, T, invs, np.array(S2, dtype=np.int64), D)
            if tabu_until.get(i, -1) > it and v >= best_cost:
                continue  # frozen coordinate, and no aspiration
            if move_val is None or v < move_val:
                move, move_val = (i, c), v
        if move is None:
            continue
        i, c = move
        S[i] = c
        cur = move_val
        tabu_until[i] = it + TABU_LEN
        if cur < best_cost:
            best_cost, best_S = cur, list(S)
    return best_S if best_cost == 0 else None


def _cycle(D):
    """Cycle C_{2D}: bipartite, 2-regular, diameter D."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite with max degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best
    if d == 1:
        return best
    if d == 2:
        n, e = _cycle(D)
        if lib.is_valid(n, e, d, D):
            return n, e
        return best

    moore = lib._moore_bound(d, D)

    # Calibration/structured case: PG(2, d-1) incidence is optimal for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    best_n = best[0]
    while time.monotonic() < deadline and best_n < moore:
        # Need 2N > best_n; sweep N upward with a bias toward the smallest orders.
        lo = max(d, best_n // 2 + 1)
        N = lo + int((rng.random() ** 2) * ORDER_WINDOW)
        if 2 * N > moore:
            break
        groups = _groups(N)
        if not groups:
            continue
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            order, T, invs = _tables(m, k, r)
            S = _tabu(order, T, invs, d, D, rng, deadline, TABU_ITERS)
            if S is not None:
                found = (order, T, S)
                break
        if found is None:
            continue
        order, T, S = found
        edges = [(x, order + int(T[x][g])) for x in range(order) for g in S]
        n = 2 * order
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
