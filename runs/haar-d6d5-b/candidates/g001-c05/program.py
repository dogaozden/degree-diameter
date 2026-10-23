import math
import random
import time

import lib

CHUNK = 2.0      # seconds of annealing per (order, group) attempt
WINDOW = 3       # orders tried above the current best


def _cost(S, N, M, I):
    """Uncovered elements for Haar connection set S: 0 iff diameter <= 5 (proved criterion)."""
    inv_S = [I[s] for s in S]
    X1 = {M[x][t] for x in inv_S for t in S}     # S^-1 S
    X2 = {M[s][y] for s in S for y in inv_S}     # S S^-1
    P1 = {M[x][y] for x in X1 for y in X1}       # (S^-1 S)^2
    P2 = {M[x][y] for x in X2 for y in X2}       # (S S^-1)^2
    return (N - len(P1)) + (N - len(P2))


def _anneal(d, N, M, I, rng, t_end):
    """Simulated annealing over d-subsets of G; returns S with cost 0, or None on timeout."""
    S = rng.sample(range(N), d)
    c = _cost(S, N, M, I)
    T = 1.0
    steps = 0
    while c > 0:
        if steps % 64 == 0 and time.monotonic() >= t_end:
            return None
        steps += 1
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        S2 = S[:]
        S2[i] = g
        c2 = _cost(S2, N, M, I)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.05, T * 0.999)
    return S


def _groups(N):
    """Candidate groups of order N as keys (N, m, k, r); m == 0 means cyclic Z_N."""
    out = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        cnt = 0
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((N, m, k, r))
                cnt += 1
                if cnt >= 3:
                    break
    out.append((N, 0, 0, 0))  # cyclic, tried last (abelian words are wasteful)
    return out


def _tables(gk, cache):
    if gk in cache:
        return cache[gk]
    N, m, k, r = gk
    if m == 0:
        order, mul, inv = lib.cyclic_group(N)
    else:
        order, mul, inv = lib.semidirect_group(m, k, r)
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    cache[gk] = (M, I)
    return M, I


def _haar(N, M, S):
    """A-vertex g is g, B-vertex h is N+h; edges (g, A) ~ (s*g, B) for s in S."""
    edges = [(g, N + M[s][g]) for s in S for g in range(N)]
    return 2 * N, edges


def _search_d5(d, D, deadline, seed):
    rng = random.Random(seed)
    best = None
    best_N = d - 1
    cache = {}
    while time.monotonic() < deadline:
        progressed = False
        for N in range(max(best_N + 1, d), best_N + WINDOW + 1):
            for gk in _groups(N):
                if time.monotonic() >= deadline:
                    return best
                M, I = _tables(gk, cache)
                S = _anneal(d, N, M, I, rng, min(deadline, time.monotonic() + CHUNK))
                if S is None:
                    continue
                n, edges = _haar(N, M, S)
                if lib.is_valid(n, edges, d, D):
                    best, best_N, progressed = (n, edges), N, True
                    break
            if progressed:
                break
        if progressed:
            for key in [key for key in cache if key[0] <= best_N]:
                del cache[key]
    return best


def _fallback(d, D, deadline, seed):
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
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
    deadline = start + 0.8 * time_limit - 1.0
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 5 and d >= 2:
        res = _search_d5(d, D, deadline, seed)
        if res is not None:
            return res
    return _fallback(d, D, deadline, seed)
