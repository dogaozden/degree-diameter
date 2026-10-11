import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) graphs over finite groups.
#
# For a group G of order N and a connection set S = {s_1..s_d} with identity in S:
#   a_g is adjacent to b_{g*s} for every s in S.
# Left multiplication by G is an automorphism acting regularly on both sides, so
# the graph has diameter <= D iff BFS from a_e and from b_e reaches everything
# within D steps. This is a different family from the voltage lifts over small
# base graphs: here the base graph is a single pair of vertices and the whole
# structure comes from one non-abelian or abelian group.
# ----------------------------------------------------------------------------

def _sample_group(N, rng):
    """Return a multiplication function on 0..N-1 (identity 0) for a random group of order N, or None."""
    u = rng.random()
    if u < 0.15:
        return lambda x, y, N=N: (x + y) % N
    if u < 0.4:
        cand = [a for a in range(2, N) if N % a == 0 and N // a >= 2]
        if not cand:
            return None
        a = rng.choice(cand)
        b = N // a

        def mul(x, y, a=a, b=b):
            x1, x2 = divmod(x, b)
            y1, y2 = divmod(y, b)
            return ((x1 + y1) % a) * b + (x2 + y2) % b
        return mul
    cand = [k for k in range(2, N // 2 + 1) if N % k == 0]
    if not cand:
        return None
    k = rng.choice(cand)
    m = N // k
    rs = [r for r in rng.sample(range(1, m), min(m - 1, 40))
          if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    if not rs:
        return None
    return lib.semidirect_group(m, k, rng.choice(rs))[1]


def _cover_bad(N, D, Ps, Qs):
    """Number of (source, vertex) pairs not reached within D, for sources a_e and b_e.

    Ps[i][g] = g*s_i, Qs[i] is its inverse permutation. Zero iff the graph has diameter <= D.
    """
    total = 0
    for side in (0, 1):
        visA = bytearray(N)
        visB = bytearray(N)
        if side == 0:
            visA[0] = 1
            fa, fb = [0], []
        else:
            visB[0] = 1
            fa, fb = [], [0]
        for _ in range(D):
            if not fa and not fb:
                break
            nb = []
            for a in fa:
                for P in Ps:
                    h = P[a]
                    if not visB[h]:
                        visB[h] = 1
                        nb.append(h)
            na = []
            for b in fb:
                for Q in Qs:
                    g = Q[b]
                    if not visA[g]:
                        visA[g] = 1
                        na.append(g)
            fa, fb = na, nb
        total += 2 * N - (sum(visA) + sum(visB))
    return total


def _search(N, d, D, mul, rng, deadline, iters):
    """Anneal a connection set S (|S| = d, identity in S) so the bi-Cayley graph has diameter <= D."""
    if d < 2 or N < d + 1:
        return None
    cache = {}

    def get(s):
        pr = cache.get(s)
        if pr is None:
            P = [mul(g, s) for g in range(N)]
            Q = [0] * N
            for g, h in enumerate(P):
                Q[h] = g
            pr = (P, Q)
            cache[s] = pr
        return pr

    def ev(S):
        prs = [get(s) for s in S]
        return _cover_bad(N, D, [p for p, _ in prs], [q for _, q in prs])

    S = [0] + rng.sample(range(1, N), d - 1)
    c = ev(S)
    T = 1.0
    for it in range(iters):
        if c == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        T2 = list(S)
        T2[i] = x
        c2 = ev(T2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T2, c2
        T = max(0.2, T * 0.997)
    return S if c == 0 else None


def _haar_edges(N, mul, S):
    """Edges of the bi-Cayley graph: a_g = g, b_h = N + h, a_g ~ b_{g*s} for s in S."""
    edges = []
    for s in S:
        for g in range(N):
            edges.append((g, N + mul(g, s)))
    return edges


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Algebraic candidates (cheap, exact).
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            n0, e0 = lib.projective_plane_incidence(d - 1)
            consider(n0, e0)
        except Exception:
            pass
    q = d - 2
    if D >= 3 and q >= 3 and lib.is_prime_power(q):
        try:
            n1, e1 = lib.araujo_lopez_graph(q)
            consider(n1, e1)
        except Exception:
            pass

    # Main search: bi-Cayley graphs over random groups of order N, climbing N.
    if d >= 2:
        while time.monotonic() < deadline and best_n < moore:
            half = best_n // 2
            if half + 1 > moore // 2:
                break
            step = max(1, half // 40)
            N = half + 1 + rng.randrange(step)
            if N > moore // 2:
                N = half + 1
            slice_end = min(deadline, time.monotonic() + max(1.0, 0.03 * time_limit))
            found = False
            while not found and time.monotonic() < slice_end:
                mul = _sample_group(N, rng)
                if mul is None:
                    continue
                S = _search(N, d, D, mul, rng, slice_end, 3000)
                if S is not None:
                    consider(2 * N, _haar_edges(N, mul, S))
                    found = True

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
