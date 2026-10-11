import math
import random
import time

import lib


def _table(group):
    """Expand (order, mul, inv) into a multiplication table T and inverse list I."""
    order, mul, inv = group
    T = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return order, T, I


def _groups_of_order(N, rng):
    """Cyclic Z_N plus a couple of random semidirect products Z_m x| Z_k with m*k = N."""
    groups = [_table(lib.cyclic_group(N))]
    cands = []
    for k in range(2, 9):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    for m, k, r in cands[:2]:
        groups.append(_table(lib.semidirect_group(m, k, r)))
    return groups


def _cost(S, G, D):
    """Number of (source, target) pairs not within distance D, counted from a_e and from b_e.

    The Haar-type graph a_g ~ b_{g*s} (s in S) is vertex-transitive on each side under left
    translation, so checking BFS from a_e and from b_e is enough to certify diameter <= D.
    """
    N, T, I = G
    invS = [I[s] for s in S]
    adjA = [[row[s] for s in S] for row in T]       # a_g -> b_{g*s}
    adjB = [[row[t] for t in invS] for row in T]    # b_y -> a_{y*s^-1}
    total = 0
    for side in (0, 1):
        vA = bytearray(N)
        vB = bytearray(N)
        if side == 0:
            vA[0] = 1
            fA, fB = [0], []
        else:
            vB[0] = 1
            fA, fB = [], [0]
        for _ in range(D):
            nA, nB = [], []
            for g in fA:
                for y in adjA[g]:
                    if not vB[y]:
                        vB[y] = 1
                        nB.append(y)
            for y in fB:
                for g in adjB[y]:
                    if not vA[g]:
                        vA[g] = 1
                        nA.append(g)
            fA, fB = nA, nB
            if not fA and not fB:
                break
        total += 2 * N - sum(vA) - sum(vB)
    return total


def _search(G, D, d, rng, iters):
    """Hill-climb a d-element connection set S (distinct elements) with cost 0 if possible."""
    N = G[0]
    if N < d:
        return None
    S = rng.sample(range(N), d)
    c = _cost(S, G, D)
    for _ in range(iters):
        if c == 0:
            return S
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost(S2, G, D)
        if c2 <= c or rng.random() < 0.03:
            S, c = S2, c2
    return S if c == 0 else None


def _edges(G, S):
    N, T, _ = G
    return [(g, N + T[g][s]) for g in range(N) for s in S]


def _attempt(N, d, D, rng, deadline):
    """Try to find a valid group-Haar graph with 2N vertices before the deadline."""
    groups = _groups_of_order(N, rng)
    while time.monotonic() < deadline:
        for G in groups:
            S = _search(G, D, d, rng, 300)
            if S is not None:
                n, edges = 2 * N, _edges(G, S)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            if time.monotonic() >= deadline:
                break
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2
    lo, hi = d, None  # lo: largest feasible group order found, hi: smallest failing one

    while time.monotonic() < deadline:
        if hi is None:
            N = lo + max(1, lo // 6)
        elif hi - lo > 1:
            N = (lo + hi) // 2
        else:
            N = hi  # retry the boundary with fresh randomness
        budget = min(deadline, time.monotonic() + 4.0)
        res = _attempt(N, d, D, rng, budget)
        if res is not None:
            lo, best = N, res
            if hi is not None and hi <= lo:
                hi = None
        else:
            hi = N

    return best
