import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph (exact for D = 3 when d-1 is a
# prime power). Used as a safe starting point, never returned unless valid.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW construction: bi-Cayley (Haar-type) graphs over NON-cyclic groups.
#
# Let G be a finite group with identity 0 and a fixed d-subset S of G.
# Vertices: A-side x in G (index x) and B-side y in G (index N + y).
# Edge x -- N+y iff x^{-1} y in S, i.e. y = x s.
# Degree is exactly d (S distinct). Bipartite by construction.
#
# Left multiplication by G is an automorphism, so the diameter is at most D
# iff every vertex is within D of the two identities (A-side e and B-side e).
# That is just two BFS runs, which makes the search cheap.
#
# Search: simulated annealing on S, minimising the number of unreached pairs.
# Groups: semidirect products Z_m x| Z_k (possibly times a cyclic factor),
# which are generally non-abelian and give structure cyclic lifts lack.
# ----------------------------------------------------------------------------

_KS = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30]
_JS = [1, 1, 1, 1, 2, 3, 4]


def _semi_table(m, k, r):
    """Multiplication table of Z_m x| Z_k: (a,b)(c,e) = (a + r^b c, b + e), element a*k + b."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return M


def _prod_table(M1, M2):
    """Direct product of two groups given by multiplication tables; element x1*N2 + x2."""
    N1, N2 = M1.shape[0], M2.shape[0]
    return (M1[:, None, :, None] * N2 + M2[None, :, None, :]).reshape(N1 * N2, N1 * N2)


def _sample_group(target, rng):
    """Return (M, inv, N) for a group of order N >= target (roughly), or None."""
    j = rng.choice(_JS)
    t = -(-target // j)
    k = rng.choice(_KS)
    m = max(2, -(-t // k))
    if k == 1:
        r = 1
    else:
        r = None
        for _ in range(80):
            c = rng.randrange(1, m)
            if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                r = c
                break
        if r is None:
            return None
    M = _semi_table(m, k, r)
    if j > 1:
        M = _prod_table(M, _semi_table(1, j, 1))
    N = M.shape[0]
    inv = np.empty(N, dtype=np.int64)
    rows, cols = np.nonzero(M == 0)
    inv[rows] = cols
    return M, inv, N


def _evaluate(M, inv, N, S, D):
    """Return (unreached pairs from the two identities, neighbour array) for connection set S."""
    S = np.asarray(S, dtype=np.int64)
    n2 = 2 * N
    nbr = np.empty((n2, len(S)), dtype=np.int64)
    nbr[:N] = N + M[:, S]          # A-vertex x -> B-vertex x*s
    nbr[N:] = M[:, inv[S]]         # B-vertex y -> A-vertex y*s^{-1}
    total = 0
    for src in (0, N):
        seen = np.zeros(n2, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = nbr[fr].ravel()
            nb = np.unique(nb[~seen[nb]])
            if nb.size == 0:
                break
            seen[nb] = True
            fr = nb
        total += n2 - int(seen.sum())
    return total, nbr


def _anneal(M, inv, N, d, D, rng, deadline, iters):
    """Anneal a d-subset S of G so that the bi-Cayley graph has diameter <= D. Returns S or None."""
    if N < d:
        return None
    S = rng.sample(range(N), d)
    cost, _ = _evaluate(M, inv, N, S, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        cand = list(S)
        cand[i] = new
        c, _ = _evaluate(M, inv, N, cand, D)
        T = max(0.15, 1.5 * (1.0 - t / iters))
        if c <= cost or rng.random() < math.exp(-(c - cost) / T):
            S, cost = cand, c
    return S if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe baseline: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: grow the bi-Cayley order over randomly sampled groups.
    if d >= 3 and D >= 3:
        while time.monotonic() < deadline:
            n_best = best[0]
            target = n_best // 2 + 1 + rng.randrange(0, 2)
            g = _sample_group(target, rng)
            if g is None:
                continue
            M, inv, N = g
            if 2 * N <= n_best:
                continue
            S = _anneal(M, inv, N, d, D, rng, deadline, 2500)
            if S is None:
                continue
            _, nbr = _evaluate(M, inv, N, S, D)
            n = 2 * N
            edges = [(x, int(v)) for x in range(N) for v in nbr[x]]
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
