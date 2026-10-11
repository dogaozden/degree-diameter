import math
import random
import time

import lib


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ------------------------------------------------ bi-Cayley covering search (D = 3)
#
# Let G be a group of order N and S a d-subset of G with identity e in S.
# Bipartite graph: a_x ~ b_{x s} for x in G, s in S (order 2N, d-regular).
# Left multiplication by G is an automorphism, so the diameter is <= 3 iff
#   S S^{-1} = G   (a-vertices within distance 2 of a_e)
#   S^{-1} S = G   (b-vertices within distance 2 of b_e)
# (the remaining distance-3 conditions then follow).
# Since |S S^{-1}| <= d^2 - d + 1, we need N <= d^2 - d + 1, giving up to 2(d^2-d+1) vertices.
# Groups: metacyclic Z_m x|_r Z_k, which includes cyclic and abelian products.

def _group_candidates(N):
    """Metacyclic groups of order N as (m, k, r) triples for lib.semidirect_group."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            out.append((1, k, 0))
        elif k == 1:
            out.append((m, 1, 1))
        else:
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    out.append((m, k, r))
    return out


def _tables(N, mul, inv):
    """Multiplication and inverse tables; identity is element 0."""
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    return M, I


def _miss(S, M, I, N):
    """Number of group elements missed by S S^{-1} and by S^{-1} S (0 means diameter-3 covering)."""
    A = set()
    B = set()
    for s in S:
        Ms = M[s]
        Is = I[s]
        for t in S:
            A.add(Ms[I[t]])
            B.add(M[Is][t])
    return 2 * N - len(A) - len(B)


def _anneal(d, N, M, I, rng, deadline):
    """Find S (size d, 0 in S) with S S^{-1} = S^{-1} S = G by annealing with restarts, or None."""
    if d > N or d < 2:
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), d - 1)
        inS = set(S)
        cur = _miss(S, M, I, N)
        T = 0.5
        steps = 0
        while cur > 0 and steps < 20000:
            steps += 1
            if steps % 128 == 0 and time.monotonic() >= deadline:
                return None
            idx = rng.randrange(1, d)
            new = rng.randrange(1, N)
            if new in inS:
                continue
            old = S[idx]
            S[idx] = new
            c2 = _miss(S, M, I, N)
            if c2 <= cur or rng.random() < math.exp((cur - c2) / T):
                inS.discard(old)
                inS.add(new)
                cur = c2
            else:
                S[idx] = old
        if cur == 0:
            return S
    return None


def _group_search(d, floor_N, hi, rng, deadline):
    """Search groups of order N in (floor_N, hi], largest first, with growing per-candidate budgets.

    Returns (n, edges) for a graph with n = 2N > 2*floor_N, or None.
    """
    entries = []
    for N in range(hi, floor_N, -1):
        for g in _group_candidates(N):
            entries.append([N, g, None])
    bestN, best = floor_N, None
    budget = 0.02
    while entries and time.monotonic() < deadline:
        entries = [e for e in entries if e[0] > bestN]
        for e in entries:
            now = time.monotonic()
            if now >= deadline:
                break
            N = e[0]
            if e[2] is None:
                _, mul, inv = lib.semidirect_group(*e[1])
                e[2] = _tables(N, mul, inv)
            M, I = e[2]
            S = _anneal(d, N, M, I, rng, min(deadline, now + budget))
            if S is not None and N > bestN:
                bestN, best = N, (S, M)
        budget *= 2
    if best is None:
        return None
    S, M = best
    edges = [(x, bestN + M[x][s]) for x in range(bestN) for s in S]
    return 2 * bestN, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
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
        # Structured bases: projective plane (Moore-optimal when d-1 is a prime power),
        # or the Araujo-Pardo-Lopez graph.
        base = None
        q = d - 1
        if lib.is_prime_power(q):
            base = lib.projective_plane_incidence(q)
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            base = lib.araujo_lopez_graph(d - 2)
        if base is not None and lib.is_valid(base[0], base[1], d, D) and base[0] > best[0]:
            best = base

        # Bold change: bi-Cayley covering search over metacyclic groups.
        mb = _moore(d, D)
        if best[0] < mb:
            hi = d * d - d + 1
            floor_N = best[0] // 2
            if hi > floor_N:
                res = _group_search(d, floor_N, hi, rng, deadline)
                if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                    best = res
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
