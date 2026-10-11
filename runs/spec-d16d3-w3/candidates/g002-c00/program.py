import math
import random
import time

import lib


# Bold change: a different family for D = 3. The bipartite Haar graph H(m, S)
# has parts Z_m and vertices a_i ~ b_{i+s} for s in S, with |S| = d. It is
# bipartite, is d-regular, and has diameter at most 3 exactly when S - S
# covers all of Z_m. So the task becomes a difference-covering search: find S
# with |S| = d and S - S = Z_m, for the largest possible m. The order is 2m,
# and the Moore-type ceiling is m <= d(d-1)+1. The earlier arc-extension is
# kept as a candidate, and the K_{d,d} fallback is always present.


def _pg_nbr(q):
    """Return (m, edges, nbr) for PG(2, q); nbr[x] = indices incident to x."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)
    return m, edges, nbr


def _conic_init(q):
    """Conic (plus nucleus for even q) as an index set, same ordering as lib.projective_points."""
    pts = lib.projective_points(q)
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


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


def _cover_search(k, m, rng, deadline):
    """Find S subset of Z_m, |S| = k, with S - S = Z_m (nonzero residues all covered), by simulated annealing.

    Returns the list S on success, or None if the deadline passes first.
    """
    if m < k:
        return None
    S = rng.sample(range(m), k)
    inS = [False] * m
    for x in S:
        inS[x] = True
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)
    T = 0.4
    it = 0
    while unc > 0:
        it += 1
        if (it & 511) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        x = S[i]
        v = rng.randrange(m)
        if inS[v]:
            continue
        others = [S[j] for j in range(k) if j != i]
        delta = 0
        # Remove x: its ordered differences leave the count table.
        for y in others:
            r = (x - y) % m
            cnt[r] -= 1
            if cnt[r] == 0:
                delta += 1
            r = (y - x) % m
            cnt[r] -= 1
            if cnt[r] == 0:
                delta += 1
        # Add v.
        for y in others:
            r = (v - y) % m
            if cnt[r] == 0:
                delta -= 1
            cnt[r] += 1
            r = (y - v) % m
            if cnt[r] == 0:
                delta -= 1
            cnt[r] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = v
            inS[x] = False
            inS[v] = True
            unc += delta
        else:
            # Undo: remove v's differences, then restore x's.
            for y in others:
                cnt[(v - y) % m] -= 1
                cnt[(y - v) % m] -= 1
            for y in others:
                cnt[(x - y) % m] += 1
                cnt[(y - x) % m] += 1
    return S


def _haar_search(k, rng, deadline):
    """Return (m, S) with the largest m found such that S - S = Z_m and |S| = k, or None."""
    M = k * (k - 1) + 1  # counting bound for S - S = Z_m
    m = max(k, int(0.7 * M))
    best = None
    fails = 0
    while m <= M and fails < 3:
        now = time.monotonic()
        rem = deadline - now
        if rem < 0.2:
            break
        budget = max(0.5, 0.35 * rem)
        S = _cover_search(k, m, rng, min(deadline, now + budget))
        if S is not None:
            best = (m, S)
            fails = 0
        else:
            fails += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every d >= 1.
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

        # Conic arc extensions (deterministic; validated by consider).
        for q in range(2, d - 1):
            if q > 23 or not lib.is_prime_power(q):
                continue
            s = d - q - 1
            if s < 1:
                continue
            m, edges, nbr = _pg_nbr(q)
            consider(*_arc_graph(m, edges, nbr, _conic_init(q)))

        # Bold path: bipartite Haar graph from a difference cover of Z_m.
        found = _haar_search(d, rng, deadline)
        if found is not None:
            m, S = found
            consider(*lib.haar_graph(m, S))

    return best
