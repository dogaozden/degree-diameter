import math
import random
import time

import lib


# Bold change: instead of growing the PG/Araujo-Lopez base by edge-switch annealing,
# build bipartite Haar-type lifts over finite groups G of order N:
#   A-vertices x, B-vertices y, A-x ~ B-(x*s) for s in S, |S| = d.
# Such a graph is d-regular and bipartite. It has diameter <= 3 exactly when
#   S S^{-1} = G  and  S^{-1} S = G  (difference-cover condition).
# So the task becomes: find a d-subset S of a group of order N with both covers,
# for the largest N possible. Order 2N beats the structured base when N > base_n / 2.
# Safe fallbacks: the structured base (verified) and then the parent's random Haar search.


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _make_cover(group, d):
    """Precompute multiplication and inverse tables for a group (order, mul, inv)."""
    N, mul, inv = group
    I = [inv(x) for x in range(N)]
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    e = M[0][I[0]]  # identity: x * x^{-1}
    return (N, d, M, I, e, mul)


def _anneal(C, rng, deadline):
    """Search a d-subset S with S S^{-1} = G and S^{-1} S = G by incremental simulated annealing.

    Cost = (uncovered elements of S S^{-1}) + (uncovered elements of S^{-1} S).
    Returns S when cost is 0, or None if the deadline passes first.
    """
    N, d, M, I, e, _mul = C
    if N <= d:
        return None
    S = rng.sample(range(N), d)
    inS = [False] * N
    c1 = [0] * N
    c2 = [0] * N
    cov = [0, 0]

    def upd(x, others, sign):
        """Add (sign=+1) or remove (sign=-1) all ordered pairs involving x, given the other elements."""
        Ix = I[x]
        p1 = [e]
        p2 = [e]
        for t in others:
            It = I[t]
            p1.append(M[x][It])
            p1.append(M[t][Ix])
            p2.append(M[It][x])
            p2.append(M[Ix][t])
        for p in p1:
            if sign > 0:
                c1[p] += 1
                if c1[p] == 1:
                    cov[0] += 1
            else:
                c1[p] -= 1
                if c1[p] == 0:
                    cov[0] -= 1
        for p in p2:
            if sign > 0:
                c2[p] += 1
                if c2[p] == 1:
                    cov[1] += 1
            else:
                c2[p] -= 1
                if c2[p] == 0:
                    cov[1] -= 1

    for idx, x in enumerate(S):
        upd(x, S[:idx], 1)
        inS[x] = True
    cur = 2 * N - cov[0] - cov[1]
    it = 0
    seg = 20000
    T0, T1 = 1.5, 0.08
    while cur > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        frac = (it % seg) / seg
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(d)
        x = S[i]
        others = S[:i] + S[i + 1:]
        y = rng.randrange(N)
        while inS[y]:
            y = rng.randrange(N)
        upd(x, others, -1)
        upd(y, others, 1)
        new = 2 * N - cov[0] - cov[1]
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            inS[x] = False
            inS[y] = True
            S[i] = y
        else:
            upd(y, others, -1)
            upd(x, others, 1)
    return S


def _groups(N, rng, max_groups):
    """Return up to max_groups groups of order N: the cyclic group plus some semidirect products Z_m x| Z_k."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                cands.append((m, k, r))
    rng.shuffle(cands)
    groups = [lib.cyclic_group(N)]
    for m, k, r in cands[: max_groups - 1]:
        groups.append(lib.semidirect_group(m, k, r))
    return groups


def _search(d, D, rng, deadline, N0):
    """Find the largest N >= N0 for which a valid group Haar graph of order 2N is found by the deadline."""
    best = None
    N = max(N0, d)
    while time.monotonic() < deadline and N <= d * (d - 1) + 1:
        covers = [_make_cover(g, d) for g in _groups(N, rng, 6)]
        found = None
        sl = 0.5
        while found is None and time.monotonic() < deadline:
            for C in covers:
                now = time.monotonic()
                if now >= deadline:
                    break
                S = _anneal(C, rng, min(deadline, now + sl))
                if S is not None:
                    found = (C, S)
                    break
            sl *= 2
        if found is None:
            break
        C, S = found
        n, edges = lib.group_lift(2, [(0, 1, s) for s in S], C[0], C[5])
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            N += 1
        else:
            break
    return best


def _fallback(d, D, rng, deadline):
    """Parent-style random Haar search (diameter checked directly), with K_{d,d} as the floor."""
    best = lib.haar_graph(d, range(d))
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    best = None
    base_n = 0

    # Structured bases for D = 3 (verified; used as the safe fallback).
    if D == 3:
        q = d - 1
        base = None
        if q >= 2 and lib.is_prime_power(q):
            base = lib.projective_plane_incidence(q)
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            base = lib.araujo_lopez_graph(d - 2)
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            best = base
            base_n = base[0]

    # New construction: group Haar graphs with difference-cover condition (diameter 3).
    if D >= 3 and d >= 3:
        N0 = base_n // 2 + 1 if best is not None else d
        cand = _search(d, D, rng, deadline, N0)
        if cand is not None and (best is None or cand[0] > best[0]):
            best = cand

    if best is None:
        best = _fallback(d, D, rng, deadline)

    if best is None or not lib.is_valid(best[0], best[1], d, D):
        if lib.is_valid(2, [(0, 1)], d, D):
            best = (2, [(0, 1)])
        else:
            best = (1, [])
    return best
