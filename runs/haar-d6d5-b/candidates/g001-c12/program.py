import math
import random
import time

import lib

SLICE = 3.0      # seconds of annealing per group attempt
K_CANDS = 6      # replacement candidates per annealing step
TEMP = 0.7       # Metropolis temperature
STALL_LIMIT = 400


def _cyclic_search(d, D, rng, deadline):
    """Parent's cyclic Haar search: returns a valid (n, edges); K_{d,d} is the fallback."""
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


def _group_candidates(lo, hi):
    """Semidirect products Z_m x|_r Z_k (non-abelian, r != 1) with order N = m*k in [lo, hi]."""
    out = []
    for N in range(max(lo, 6), hi + 1):
        for k in range(2, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    out.append((N, m, k, r))
    return out


def _table(m, k, r):
    """Full multiplication and inverse tables for the group; identity is element 0."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    return N, T, I


def _cost(S, N, T, I):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    Si = [I[s] for s in S]
    P = {T[a][b] for a in Si for b in S}
    P2 = {T[x][y] for x in P for y in P}
    Q = {T[a][b] for a in S for b in Si}
    Q2 = {T[x][y] for x in Q for y in Q}
    return (N - len(P2)) + (N - len(Q2))


def _anneal(d, N, T, I, rng, t_end):
    """Anneal a d-element connection set containing the identity; returns (best_cost, best_S)."""

    def rand_set():
        return [0] + rng.sample(range(1, N), d - 1)

    S = rand_set()
    cur = _cost(S, N, T, I)
    best_cost, best_S = cur, list(S)
    stall = 0
    while cur > 0 and time.monotonic() < t_end:
        i = rng.randrange(1, d)
        inS = set(S)
        cand_best = None
        for _ in range(K_CANDS):
            g = rng.randrange(1, N)
            if g in inS:
                continue
            S2 = list(S)
            S2[i] = g
            c = _cost(S2, N, T, I)
            if cand_best is None or c < cand_best[0]:
                cand_best = (c, g)
        if cand_best is None:
            continue
        c, g = cand_best
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            S[i] = g
            cur = c
        if cur < best_cost:
            best_cost, best_S = cur, list(S)
            stall = 0
        else:
            stall += 1
        if stall > STALL_LIMIT:
            S = rand_set()
            cur = _cost(S, N, T, I)
            stall = 0
    return best_cost, best_S


def _haar_from_group(N, T, S):
    """Haar graph: A_g ~ B_{s g} for s in S; A-vertex g is g, B-vertex g is N + g."""
    edges = [(g, N + T[s][g]) for s in S for g in range(N)]
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit - 1.0
    end = start + budget
    rng = random.Random(seed)

    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    if D != 5 or d < 3:
        return _cyclic_search(d, D, rng, end)

    # Phase 0: cyclic Haar search as a safe baseline (small share of the budget).
    best = _cyclic_search(d, D, rng, start + 0.15 * budget)
    best_order = best[0] // 2

    # Phase 1: non-abelian group Haar search, climbing in group order.
    hi = min(lib.moore_bound(d, D) // 2, 480)
    cands = _group_candidates(best_order + 1, hi)
    lo = best_order + 1
    while time.monotonic() < end - 0.5 and cands:
        window = [c for c in cands if lo <= c[0] <= lo + 30]
        if not window:
            if lo > hi:
                break
            lo += 1
            continue
        N, m, k, r = rng.choice(window)
        Ng, T, I = _table(m, k, r)
        slice_end = min(end, time.monotonic() + SLICE)
        cost, S = _anneal(d, Ng, T, I, rng, slice_end)
        if cost == 0:
            n, edges = _haar_from_group(Ng, T, S)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_order = Ng
                lo = Ng + 1

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return lib.haar_graph(d, range(d))
