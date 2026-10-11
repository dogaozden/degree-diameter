import math
import random
import time

import lib


def _groups(N, rng, cap):
    """Candidate groups of order N as (mul, inv) pairs with identity 0.

    Includes the cyclic group and every semidirect product Z_m x| Z_k with m*k = N
    that lib.semidirect_group accepts. The list is shuffled and capped.
    """
    cands = [lib.cyclic_group(N)[1:]]
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                _, mul, inv = lib.semidirect_group(m, k, r)
                cands.append((mul, inv))
    rng.shuffle(cands)
    return cands[:cap]


def _cost(S, N, mul, inv, D):
    """Number of (source, vertex) pairs left unreached within radius D.

    The Haar graph H(G, S) has vertices a_x, b_y (x, y in G) with a_x ~ b_{x*s}.
    Left multiplication by g is an automorphism, so all A-vertices are equivalent
    and all B-vertices are equivalent. Hence zero cost from a_e and b_e certifies
    diameter <= D for the whole graph.
    """
    invS = [inv(s) for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    for s in S:
                        w = N + mul(v, s)
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    y = v - N
                    for si in invS:
                        w = mul(y, si)
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            frontier = nxt
            cnt += len(nxt)
            if not frontier:
                break
        total += 2 * N - cnt
    return total


def _anneal(N, mul, inv, d, D, rng, limit):
    """Local search over d-element connection sets S in G, minimising _cost.

    Returns S with zero cost, or None if the time limit is reached first.
    """
    if d > N:
        return None
    S = rng.sample(range(N), d)
    c = _cost(S, N, mul, inv, D)
    temp = 1.0
    while c > 0:
        if time.monotonic() > limit:
            return None
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        S2 = S[:]
        S2[i] = t
        c2 = _cost(S2, N, mul, inv, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, c = S2, c2
        temp = max(0.2, temp * 0.99)
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)

    # Exact extremal case: projective plane incidence graph.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = (2, [(0, 1)]) if D >= 1 else (1, [])
    if D >= 2 and d >= 2:
        best = lib.haar_graph(d, range(d))

    # New idea: ascending search over group orders N. Each candidate is a bipartite
    # Haar graph over a group of order N (cyclic or semidirect product) with a
    # d-element connection set. Vertex-transitivity lets a two-source BFS certify
    # diameter. Feasibility is not monotone in N, so stop only after a streak of
    # consecutive failures.
    hi = lib.moore_bound(d, D) // 2
    lo = max(d, 1)
    best_info = None
    fails = 0
    N = lo
    while N <= hi and time.monotonic() < deadline and fails < 12:
        found = None
        for mul, inv in _groups(N, rng, 3):
            lim = min(deadline, time.monotonic() + 0.8)
            S = _anneal(N, mul, inv, d, D, rng, lim)
            if S is not None:
                found = (mul, S)
                break
            if time.monotonic() >= deadline:
                break
        if found is not None:
            best_info = (N, found[0], found[1])
            fails = 0
        else:
            fails += 1
        N += 1

    if best_info is not None:
        N, mul, S = best_info
        edges = [(x, N + mul(x, s)) for x in range(N) for s in S]
        n = 2 * N
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    return best
