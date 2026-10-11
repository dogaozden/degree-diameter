import math
import random
import time

import lib


# Arc-extension search for D = 3. The arc set S is a packing in the polarity
# graph of PG(2, q): every index X may have at most s = d - q - 1 members of S
# among its incident indices. This version replaces the ILS with simulated
# annealing on a penalty objective, -|S| + lam * (total excess), which lets the
# search cross infeasible states. It records the best feasible set. Time goes
# only to prime powers q whose counting upper bound can beat the current best,
# so for d = 16 the whole budget goes to q = 13.


def _pg_nbr(q):
    """Return (m, edges, nbr) for PG(2, q); nbr[x] = indices incident to x (points and lines share indices)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)  # point u lies on line v - m; the incidence matrix is symmetric
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


def _anneal(m, nbr, s, rng, deadline, init, lam=1.3, T0=0.5, T1=0.05, cycle=4.0):
    """Simulated annealing on cost = -|S| + lam * excess, excess = sum_X max(0, cnt[X] - s).

    Returns the largest feasible S seen (every X has at most s members of S in nbr[X]).
    Each cycle restarts from the best feasible set found so far.
    """
    inS = [False] * m
    cnt = [0] * m
    size = 0
    V = 0

    def load(members):
        nonlocal size, V
        for i in range(m):
            inS[i] = False
            cnt[i] = 0
        size = 0
        for v in members:
            inS[v] = True
            size += 1
            for X in nbr[v]:
                cnt[X] += 1
        V = sum(c - s for c in cnt if c > s)

    load(init)
    best = [i for i in range(m) if inS[i]] if V == 0 else []
    best_size = len(best)
    t_cycle = time.monotonic()
    T = T0
    it = 0
    while True:
        it += 1
        if (it & 1023) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            if now - t_cycle >= cycle:
                t_cycle = now
                load(best)
            frac = (now - t_cycle) / cycle
            T = T0 * (T1 / T0) ** frac

        v = rng.randrange(m)
        nv = nbr[v]
        if inS[v]:
            # Removal: size drops by 1, excess drops by the number of X with cnt > s.
            dV = 0
            for X in nv:
                if cnt[X] > s:
                    dV -= 1
            dc = 1 + lam * dV
            adding = False
        else:
            # Addition: size grows by 1, excess grows by the number of X with cnt >= s.
            dV = 0
            for X in nv:
                if cnt[X] >= s:
                    dV += 1
            dc = -1 + lam * dV
            adding = True

        if dc > 0 and rng.random() >= math.exp(-dc / T):
            continue

        if adding:
            inS[v] = True
            size += 1
            for X in nv:
                cnt[X] += 1
        else:
            inS[v] = False
            size -= 1
            for X in nv:
                cnt[X] -= 1
        V += dV

        if V == 0 and size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


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

        # Candidate q whose counting bound can beat the current best.
        # Each arc element adds q+1 incidences, and each index can absorb at most s,
        # so |S| <= s*m/(q+1), giving n <= 2*(m + floor(s*m/(q+1))).
        candidates = []
        for q in range(2, d - 1):
            if not (lib.is_prime_power(q) and q <= 23):
                continue
            s = d - q - 1
            if s < 1:
                continue
            m = q * q + q + 1
            bound = 2 * (m + (s * m) // (q + 1))
            if bound > best_n:
                candidates.append((bound, q, s))
        candidates.sort(reverse=True)

        for idx, (bound, q, s) in enumerate(candidates):
            now = time.monotonic()
            remaining = max(0.0, deadline - now)
            slice_end = now + remaining / (len(candidates) - idx)
            m, edges, nbr = _pg_nbr(q)
            S = _anneal(m, nbr, s, rng, slice_end, _conic_init(q))
            if S:
                n_arc, E_arc = _arc_graph(m, edges, nbr, S)
                consider(n_arc, E_arc)
                if n_arc >= bound:
                    break  # cannot do better for this q

    return best
