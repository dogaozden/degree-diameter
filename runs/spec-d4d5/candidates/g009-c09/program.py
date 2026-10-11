import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Repair-search family: d-regular bipartite graphs grown by vertex insertion,
# with simulated annealing over double edge swaps. Cost = number of ordered
# vertex pairs at distance > D, computed with float32 matrix products.
# ----------------------------------------------------------------------------

def _cost(N, F, D):
    """Number of ordered pairs (u, v) with dist(u, v) > D. Zero means valid."""
    R = np.eye(2 * N, dtype=np.float32)
    for _ in range(D):
        R = ((R @ F + R) > 0).astype(np.float32)
    return int(2 * N * 2 * N - R.sum())


def _make_F(N, ea, eb):
    """Symmetric 0/1 adjacency of the bipartite graph; A vertex i is i, B vertex j is N + j."""
    F = np.zeros((2 * N, 2 * N), dtype=np.float32)
    ea_arr = np.asarray(ea, dtype=np.int64)
    eb_arr = np.asarray(eb, dtype=np.int64) + N
    F[ea_arr, eb_arr] = 1.0
    F[eb_arr, ea_arr] = 1.0
    return F


def _anneal(N, ea, eb, D, rng, deadline, iters, T0, T1):
    """Annealing over double edge swaps (degrees and bipartition preserved).

    ea, eb are modified in place. Returns the final cost (0 means valid).
    """
    F = _make_F(N, ea, eb)
    exists = set(zip(ea, eb))
    cost = _cost(N, F, D)
    if cost == 0:
        return 0
    E = len(ea)
    decay = (T1 / T0) ** (1.0 / max(1, iters))
    T = T0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T *= decay
        i = rng.randrange(E)
        j = rng.randrange(E)
        if i == j:
            continue
        a1, b1, a2, b2 = ea[i], eb[i], ea[j], eb[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in exists or (a2, b1) in exists:
            continue
        # Apply swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
        F[a1, N + b1] = 0
        F[N + b1, a1] = 0
        F[a2, N + b2] = 0
        F[N + b2, a2] = 0
        F[a1, N + b2] = 1
        F[N + b2, a1] = 1
        F[a2, N + b1] = 1
        F[N + b1, a2] = 1
        c2 = _cost(N, F, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            exists.discard((a1, b1))
            exists.discard((a2, b2))
            exists.add((a1, b2))
            exists.add((a2, b1))
            eb[i] = b2
            eb[j] = b1
        else:
            # Revert.
            F[a1, N + b2] = 0
            F[N + b2, a1] = 0
            F[a2, N + b1] = 0
            F[N + b1, a2] = 0
            F[a1, N + b1] = 1
            F[N + b1, a1] = 1
            F[a2, N + b2] = 1
            F[N + b2, a2] = 1
    return cost


def _insert(N, ea, eb, d, rng):
    """Add one A vertex N and one B vertex N, each of degree d.

    Pick d edges forming a matching (a_k, b_k); remove them; join new A vertex to
    every b_k and new B vertex to every a_k. Degrees stay exactly d.
    Returns (N+1, ea2, eb2), or None if no suitable matching was found.
    """
    idx = list(range(len(ea)))
    rng.shuffle(idx)
    used_a = set()
    used_b = set()
    chosen = []
    for k in idx:
        if ea[k] not in used_a and eb[k] not in used_b:
            chosen.append(k)
            used_a.add(ea[k])
            used_b.add(eb[k])
            if len(chosen) == d:
                break
    if len(chosen) < d:
        return None
    chosen_set = set(chosen)
    nea, neb = [], []
    for k in range(len(ea)):
        if k not in chosen_set:
            nea.append(ea[k])
            neb.append(eb[k])
    for k in chosen:
        nea.append(N)          # new A vertex to old B vertex b_k
        neb.append(eb[k])
        nea.append(ea[k])      # old A vertex a_k to new B vertex
        neb.append(N)
    return N + 1, nea, neb


def _circulant(N, d):
    """d-regular bipartite circulant on N + N vertices (needs d <= N)."""
    ea, eb = [], []
    for s in range(d):
        for i in range(N):
            ea.append(i)
            eb.append((i + s) % N)
    return ea, eb


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 4.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2 or d == 1:
        return best

    if d == 2:
        # Even cycle C_{2D} has diameter D and is bipartite.
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    # Projective plane incidence graph is Moore-optimal for D = 3 when d-1 is a prime power.
    if lib.is_prime_power(d - 1):
        pg_n, pg_e = lib.projective_plane_incidence(d - 1)
        consider(pg_n, pg_e)
        if D == 3:
            return best

    rng = random.Random(seed * 1000003 + d * 31 + D)
    NMAX = 200  # keeps each cost evaluation cheap

    N = d + 1
    ea, eb = _circulant(N, d)
    cost = _anneal(N, ea, eb, D, rng, deadline, 1500, 2.0, 0.2)
    while cost != 0 and time.monotonic() < deadline:
        cost = _anneal(N, ea, eb, D, rng, deadline, 1500, 1.0, 0.2)
    if cost != 0:
        return best

    cur = (N, list(ea), list(eb))
    iters = 800
    while time.monotonic() < deadline and 2 * (cur[0] + 1) <= NMAX:
        ins = _insert(cur[0], cur[1], cur[2], d, rng)
        if ins is None:
            continue
        N2, ea2, eb2 = ins
        c = _anneal(N2, ea2, eb2, D, rng, deadline, iters, 2.0, 0.2)
        if c == 0:
            cur = (N2, ea2, eb2)
            iters = 800
            edges = [(ea2[k], N2 + eb2[k]) for k in range(len(ea2))]
            consider(2 * N2, edges)
        else:
            iters = min(iters + 400, 6000)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
