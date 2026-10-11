import math
import random
import time

import lib


def _fallback(d, D):
    """Safe baseline: K_{d,d} (valid for D >= 2), or PG(2,q) incidence when D >= 3."""
    best = lib.haar_graph(d, range(d))
    if D >= 3 and d >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                break
    return best


def _diff_uncovered(m, S):
    """Number of residues z in Z_m not of the form a - b with a, b in S.

    The Haar graph H(m, S) has diameter <= 3 exactly when this count is 0
    (same-side pairs must be within distance 2, which means S - S = Z_m).
    """
    cnt = [0] * m
    for a in S:
        for b in S:
            cnt[(a - b) % m] += 1
    return cnt.count(0)


def _bfs_bad(m, S, D):
    """Vertices not within distance D of a_0 in H(m, S).

    H(m, S) is vertex-transitive (translations plus the side swap a_i <-> b_{-i}),
    so eccentricity of a_0 being <= D means diameter <= D.
    """
    adj = [[] for _ in range(2 * m)]
    for i in range(m):
        for s in S:
            j = (i + s) % m
            adj[i].append(m + j)
            adj[m + j].append(i)
    dist = [-1] * (2 * m)
    dist[0] = 0
    frontier = [0]
    reached = 1
    for depth in range(1, D + 1):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = depth
                    nxt.append(v)
        reached += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return 2 * m - reached


def _anneal(m, k, D, rng, deadline, use_diff):
    """Search for a k-subset S of Z_m (containing 0) making H(m, S) have diameter <= D.

    Simulated annealing on the number of uncovered residues / bad vertices.
    Returns S on success, None if the deadline passes first.
    """
    if k < 2 or m < k:
        return None

    def cost(S):
        return _diff_uncovered(m, S) if use_diff else _bfs_bad(m, S, D)

    S = [0] + rng.sample(range(1, m), k - 1)
    c = cost(S)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while c > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        temp = 1.2 * (0.02 ** frac)
        i = rng.randrange(1, k)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        c2 = cost(T)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, c = T, c2
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d, D)
    k = d

    # D = 2: K_{d,d} is optimal among bipartite graphs, so the fallback is final.
    if D >= 3 and k >= 2:
        rng = random.Random(seed)
        use_diff = (D == 3)
        if use_diff:
            mmax = k * (k - 1) + 1          # hard cap: |S - S| <= k(k-1) + 1
            m = max(k, min(mmax, 170))      # start in the region of known good orders
        else:
            mmax = lib.moore_bound(d, D) // 2
            m = max(k, best[0] // 2 + 1)

        fails = 0
        while m <= mmax and time.monotonic() < deadline and fails < 2:
            now = time.monotonic()
            budget = max(1.5, 0.12 * (deadline - start))
            att_dl = min(deadline, now + budget)
            S = _anneal(m, k, D, rng, att_dl, use_diff)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                fails = 0
            else:
                fails += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
