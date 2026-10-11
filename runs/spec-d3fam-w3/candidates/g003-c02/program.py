import math
import random
import time
from math import gcd

import lib


# ----------------------------------------------------------------------------
# Non-abelian bi-Cayley (Haar-type) graphs from group difference covers.
#
# For a finite group G of order N and a d-subset S of G with 1 in S, let
#   a_x ~ b_y  iff  x^{-1} y in S.
# This graph is bipartite, d-regular, with 2N vertices, and:
#   a-a distance <= 2 iff S S^{-1} = G,
#   b-b distance <= 2 iff S^{-1} S = G,
#   a-b distance <= 3 whenever S S^{-1} = G (since g = (g s^{-1}) s for any s in S).
# The cyclic case is the parent's construction. Non-abelian groups (Z_m x| Z_k)
# give many more candidate groups of each order, so covers of size d can exist
# at orders where no cyclic cover is found.
# ----------------------------------------------------------------------------


def _semidirect_candidates(N):
    """All (m, k, r) with m*k = N giving a group Z_m x|_r Z_k (r = 0 when m = 1)."""
    cands = []
    for k in range(1, N + 1):
        if N % k:
            continue
        mm = N // k
        if mm == 1:
            cands.append((1, k, 0))
            continue
        for r in range(1, mm):
            if gcd(r, mm) == 1 and pow(r, k, mm) == 1:
                cands.append((mm, k, r))
    return cands


class _Group:
    """Multiplication and inverse tables for a group whose elements are 0..N-1 with 0 the identity."""

    def __init__(self, N, mul, inv):
        self.N = N
        self.M = [[mul(x, y) for y in range(N)] for x in range(N)]
        self.I = [inv(x) for x in range(N)]


def _anneal(G, d, rng, deadline, iters):
    """Anneal a d-subset S of G (identity included) so that S S^{-1} = G and S^{-1} S = G. Returns S or None."""
    N, M, I = G.N, G.M, G.I
    S = [0] + rng.sample(range(1, N), d - 1)
    inS = [False] * N
    for s in S:
        inS[s] = True
    A = [0] * N  # counts of s_i s_j^{-1}
    B = [0] * N  # counts of s_i^{-1} s_j
    for i in range(d):
        for j in range(d):
            if i != j:
                A[M[S[i]][I[S[j]]]] += 1
                B[M[I[S[i]]][S[j]]] += 1
    A[0] += d
    B[0] += d
    zeros = sum(1 for g in range(N) if A[g] == 0) + sum(1 for g in range(N) if B[g] == 0)

    def pairs(x, skip):
        """Coverage slots touched by placing x against every other element of S (except index skip)."""
        P = []
        Ix = I[x]
        for j in range(d):
            if j == skip:
                continue
            t = S[j]
            It = I[t]
            P.append((A, M[x][It]))
            P.append((A, M[t][Ix]))
            P.append((B, M[Ix][t]))
            P.append((B, M[It][x]))
        return P

    def dec(P):
        z = 0
        for arr, g in P:
            arr[g] -= 1
            if arr[g] == 0:
                z += 1
        return z

    def inc(P):
        z = 0
        for arr, g in P:
            if arr[g] == 0:
                z -= 1
            arr[g] += 1
        return z

    exp = math.exp
    rand = rng.random
    for it in range(iters):
        if zeros == 0:
            break
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        T = 0.8 * (0.05 / 0.8) ** (it / iters)
        idx = rng.randrange(1, d)
        old = S[idx]
        new = rng.randrange(1, N)
        if inS[new]:
            continue
        pold = pairs(old, idx)
        dz = dec(pold)
        S[idx] = new
        pnew = pairs(new, idx)
        dz += inc(pnew)
        if dz <= 0 or rand() < exp(-dz / T):
            zeros += dz
            inS[old] = False
            inS[new] = True
        else:
            dec(pnew)
            inc(pold)
            S[idx] = old
    return S if zeros == 0 else None


def _group_haar(G, S):
    """Bi-Cayley graph: a_x = x, b_y = N + y, edge a_x ~ b_{x s} for s in S."""
    N = G.N
    edges = []
    for x in range(N):
        Mx = G.M[x]
        for s in S:
            edges.append((x, N + Mx[s]))
    return 2 * N, edges


def _group_search(d, m_start, deadline, rng, consider):
    """For each order m = m_start, m_start+1, ..., find a group cover of size d and offer the graph of order 2m."""
    m = m_start
    m_max = d * (d - 1) + 1
    cache = {}
    while m <= m_max and time.monotonic() < deadline:
        cands = _semidirect_candidates(m)
        rng.shuffle(cands)
        if not cands:
            break
        found = None
        attempt = 0
        while found is None and time.monotonic() < deadline:
            cand = cands[attempt % len(cands)]
            attempt += 1
            if cand not in cache:
                mm, k, r = cand
                order, mul, inv = lib.semidirect_group(mm, k, r)
                cache[cand] = _Group(order, mul, inv)
            G = cache[cand]
            S = _anneal(G, d, rng, deadline, 40000)
            if S is not None:
                found = (G, S)
        if found is None:
            break
        G, S = found
        n, e = _group_haar(G, S)
        consider(n, e)
        m += 1


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        # Moore-optimal case: PG(2, d-1) incidence graph.
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Araujo-Pardo & Lopez record family when d-2 is a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass

    # Main search: non-abelian group difference covers (valid for any D >= 3).
    # Start just above the current best half-order so every success is a strict improvement.
    m_start = max(d, best_n // 2 + 1)
    if m_start <= d * (d - 1) + 1:
        _group_search(d, m_start, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
