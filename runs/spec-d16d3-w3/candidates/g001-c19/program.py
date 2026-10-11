import math
import random
import time

import lib


# Change in this version: the arc-extension set S is found by simulated annealing
# instead of iterated local search. The state is any subset S of the polarity graph
# on PG(2, q). The energy is -|S| + lam * P, where P = sum_X max(0, cnt[X] - s) and
# cnt[X] counts members of S in N(X). Single-vertex toggles are accepted by the
# Metropolis rule under a cyclic temperature schedule. Each cycle restarts from the
# current state, so the search can escape plateaus. The best feasible set (P = 0) is
# kept and polished greedily. Time is shared across q in proportion to the order
# upper bound 2m + 2*floor(m*s/(q+1)), since that bound comes from double counting
# incidences.


def _pg_nbr(q):
    """Return (m, edges, nbr) for PG(2, q); nbr[x] = indices incident to x (points and lines share indices)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)
    return m, edges, nbr


def _conic_init(q):
    """Conic (plus nucleus for even q) as index set, using the same ordering as lib.projective_points."""
    pts = lib.projective_points(q)
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _anneal(m, nbr, s, rng, deadline, init, lam=1.2, cycles=3):
    """Simulated annealing for a large S with every X having <= s members of S in nbr[X]."""
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    inS = [False] * m
    cnt = [0] * m
    size = 0
    pen = 0

    def add(v):
        nonlocal size, pen
        inS[v] = True
        size += 1
        for X in nbr[v]:
            if cnt[X] >= s:
                pen += 1
            cnt[X] += 1

    def remove(v):
        nonlocal size, pen
        inS[v] = False
        size -= 1
        for X in nbr[v]:
            cnt[X] -= 1
            if cnt[X] >= s:
                pen -= 1

    for v in init:
        if not inS[v]:
            add(v)

    best_size = -1
    best = []
    if pen == 0:
        best_size = size
        best = [v for v in range(m) if inS[v]]

    T0, T1 = 0.6, 0.05
    T = T0
    it = 0
    while True:
        it += 1
        if (it & 511) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            f = ((now - start) / span * cycles) % 1.0
            T = T0 * (T1 / T0) ** f
        v = rng.randrange(m)
        if inS[v]:
            dpen = 0
            for X in nbr[v]:
                if cnt[X] > s:
                    dpen -= 1
            dE = 1 + lam * dpen
            if dE <= 0 or rng.random() < math.exp(-dE / T):
                remove(v)
        else:
            dpen = 0
            for X in nbr[v]:
                if cnt[X] >= s:
                    dpen += 1
            dE = -1 + lam * dpen
            if dE <= 0 or rng.random() < math.exp(-dE / T):
                add(v)
        if pen == 0 and size > best_size:
            best_size = size
            best = [u for u in range(m) if inS[u]]

    # Greedy polish of the best feasible set.
    inB = [False] * m
    cB = [0] * m
    for v in best:
        inB[v] = True
        for X in nbr[v]:
            cB[X] += 1
    order = list(range(m))
    rng.shuffle(order)
    for v in order:
        if not inB[v] and all(cB[X] < s for X in nbr[v]):
            inB[v] = True
            for X in nbr[v]:
                cB[X] += 1
    return [u for u in range(m) if inB[u]]


def _arc_graph(m, edges, nbr, S):
    """PG(2,q) incidence plus an A-vertex per element of S (joined to its lines) and a B-vertex (joined to its points)."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in nbr[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in nbr[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Plain projective plane for the largest prime power q with q + 1 <= d.
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if pg_qs:
            consider(*lib.projective_plane_incidence(pg_qs[0]))

        # Arc-extended graphs. Candidates are ordered by their order upper bound.
        cands = []
        for q in range(2, d - 1):
            if not lib.is_prime_power(q) or q > 23:
                continue
            s = d - q - 1
            if s < 1:
                continue
            m = (q * q + q + 1)
            ub_k = (m * s) // (q + 1)
            ub_n = 2 * m + 2 * ub_k
            if ub_n > best_n:
                cands.append((ub_n, q, s))
        cands.sort(reverse=True)

        if cands:
            weights = [float(ub) ** 6 for ub, _, _ in cands]
            total_w = sum(weights) or 1.0
            span = max(0.0, deadline - time.monotonic())
            for (ub_n, q, s), w in zip(cands, weights):
                if time.monotonic() >= deadline:
                    break
                m, edges, nbr = _pg_nbr(q)
                slice_end = time.monotonic() + span * w / total_w
                init = _conic_init(q)
                S = _anneal(m, nbr, s, rng, slice_end, init)
                if S:
                    consider(*_arc_graph(m, edges, nbr, S))

    return best
