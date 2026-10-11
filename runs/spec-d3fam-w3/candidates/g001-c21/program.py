import math
import random
import time

import numpy as np

import lib


# ---------------------------------------------------------------- helpers

def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _structured_base(d):
    """Projective-plane incidence or Araujo-Pardo-Lopez graph for D = 3, or None."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


# ------------------------------------------- bi-Cayley graphs over finite groups (D = 3)
#
# Group G of order N (here semidirect products Z_m x| Z_k), connection set S of size d.
# Bi-Cayley graph: vertices (g,0) and (g,1) for g in G, edge (g,0) ~ (g*s,1) for s in S.
# It is d-regular and bipartite. Left multiplication is an automorphism that is transitive
# on each side, so diameter <= 3 is equivalent to three covering conditions, which are
# exact (not just heuristic):
#   G = S S^-1           (side-0 vertices at distance 2 from (e,0))
#   G = S^-1 S           (side-1 vertices at distance 2 from (e,1))
#   G = S u S S^-1 S     (side-1 vertices at distance 1 or 3 from (e,0))
# Covering S S^-1 needs d^2-d+1 >= N, which gives the order bound used below.
# Non-abelian groups are searched in addition to cyclic ones, using simulated
# annealing on the number of uncovered group elements.

def _groups(N):
    """All (m, k, r) with m*k = N that lib.semidirect_group accepts."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == (1 % m):
                out.append((m, k, r))
    return out


def _mul_table(m, k, r):
    """Full multiplication table M[x, y] = x*y, and inverse array I, for the semidirect group."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    M = np.empty((N, N), dtype=np.int64)
    for x in range(N):
        for y in range(N):
            M[x, y] = mul(x, y)
    I = np.array([inv(x) for x in range(N)], dtype=np.int64)
    return M, I


def _cost(S, M, I, N):
    """Total number of uncovered group elements across the three covering conditions."""
    Si = I[S]
    P1 = M[S[:, None], Si[None, :]].ravel()                    # S S^-1
    c1 = N - int(np.count_nonzero(np.bincount(P1, minlength=N)))
    P2 = M[Si[:, None], S[None, :]].ravel()                    # S^-1 S
    c2 = N - int(np.count_nonzero(np.bincount(P2, minlength=N)))
    P3 = M[P1[:, None], S[None, :]].ravel()                    # S S^-1 S
    cnt = np.bincount(P3, minlength=N)
    cnt[S] += 1                                                # plus S itself
    c3 = N - int(np.count_nonzero(cnt))
    return c1 + c2 + c3


def _search(d, N, M, I, rng, deadline):
    """Find a d-subset S of G with zero covering cost, or None if the deadline passes first."""
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cost = _cost(S, M, I, N)
    T = 0.6
    best, stale, steps = cost, 0, 0
    while cost > 0:
        steps += 1
        if steps % 128 == 0 and time.monotonic() >= deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if np.any(S == x):
            continue
        S2 = S.copy()
        S2[i] = x
        c2 = _cost(S2, M, I, N)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            S, cost = S2, c2
        if cost < best:
            best, stale = cost, 0
        else:
            stale += 1
            if stale > 4000:  # restart from a fresh random set
                S = np.array(rng.sample(range(N), d), dtype=np.int64)
                cost = _cost(S, M, I, N)
                best, stale = cost, 0
    return S


def _bicayley_phase(d, best, rng, deadline):
    """Escalate the group order N upward from the current best, searching several groups per N."""
    best_n, best_edges = best
    bound = d * d - d + 1
    N = max(d, best_n // 2 + 1)
    while N <= bound and time.monotonic() < deadline:
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for (m, k, r) in groups[:8]:
            rem = deadline - time.monotonic()
            if rem <= 0:
                break
            sub = min(rem, max(1.0, 0.3 * rem))
            M, I = _mul_table(m, k, r)
            S = _search(d, N, M, I, rng, time.monotonic() + sub)
            if S is not None:
                found = (M, S)
                break
        if found is None:
            break
        M, S = found
        # Vertices 0..N-1 are side 0; N..2N-1 are side 1.
        edges = [(g, N + int(M[g, s])) for g in range(N) for s in S.tolist()]
        n = 2 * N
        if n > best_n and lib.is_valid(n, edges, d, 3):
            best_n, best_edges = n, edges
        N += 1
    return best_n, best_edges


# ---------------------------------------------------------------- main entry point

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    kdd = lib.haar_graph(d, range(d))
    if not lib.is_valid(kdd[0], kdd[1], d, D):
        kdd = (1, [])
    best = kdd

    if D == 3 and d >= 2:
        # Structured base (projective plane or Araujo-Pardo-Lopez), kept as a candidate.
        base = _structured_base(d)
        if base is not None and base[0] > best[0] and lib.is_valid(base[0], base[1], d, D):
            best = base

        # New construction: bi-Cayley graphs over non-abelian groups, searched by annealing.
        n2, e2 = _bicayley_phase(d, best, rng, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    else:
        # Random Haar fallback for other diameters.
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
                if found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                    best = found
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return kdd
    return best
