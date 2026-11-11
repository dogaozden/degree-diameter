import math
import random
import time

import lib


def _cyclic_search(d, D, seed, deadline):
    """Fallback: random cyclic Haar graphs, as in the parent program."""
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


# ---------------------------------------------------------------- group Haar graphs
# Haar graph over a group G with connection set S (1 in S, |S| = d):
# A-vertex g joins B-vertex s*g for s in S. Right multiplication is an automorphism,
# so diameter <= 5 iff T^2 = G and U^2 = G, where T = S^-1 S and U = S S^-1.
# Cost = uncovered elements in T^2 and U^2; cost 0 means a valid graph.

def _groups(N):
    """Candidate groups of order N: the cyclic group, and non-abelian Z_m x|_r Z_k (r != 1)."""
    out = [(N, 1, 1)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Multiplication and inverse tables for the group (identity is element 0)."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    return N, M, I


def _cost(S, N, M, I):
    T = {M[I[s]][t] for s in S for t in S}
    T2 = {M[a][b] for a in T for b in T}
    U = {M[s][I[t]] for s in S for t in S}
    U2 = {M[a][b] for a in U for b in U}
    return 2 * N - len(T2) - len(U2)


def _anneal(N, M, I, d, rng, t_end, temp=0.7, patience=1500):
    """Simulated annealing over connection sets S with 0 in S. Returns S with cost 0, or None."""
    while time.monotonic() < t_end:
        S = [0] + rng.sample(range(1, N), d - 1)
        c = _cost(S, N, M, I)
        best_c, stall = c, 0
        while c > 0 and stall < patience:
            if time.monotonic() >= t_end:
                return None
            i = rng.randrange(1, d)
            x = rng.randrange(1, N)
            if x in S:
                stall += 1
                continue
            S2 = S[:]
            S2[i] = x
            c2 = _cost(S2, N, M, I)
            if c2 <= c or rng.random() < math.exp((c - c2) / temp):
                S, c = S2, c2
            if c < best_c:
                best_c, stall = c, 0
            else:
                stall += 1
        if c == 0:
            return S
    return None


def _group_search(d, D, seed, deadline):
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    N, misses = d + 1, 0
    per_try = 1.5
    while time.monotonic() < deadline and misses < 3:
        cands = _groups(N)
        rng.shuffle(cands)
        found = None
        for cand in cands[:4]:
            if time.monotonic() >= deadline:
                break
            order, M, I = _tables(*cand)
            t_end = min(deadline, time.monotonic() + per_try)
            S = _anneal(order, M, I, d, rng, t_end)
            if S is None:
                continue
            edges = [(g, order + M[s][g]) for g in range(order) for s in S]
            n = 2 * order
            if lib.is_valid(n, edges, d, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        N += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if D == 5 and d >= 3:
        best = _group_search(d, D, seed, deadline)
        if best is not None:
            return best
    return _cyclic_search(d, D, seed, deadline)
