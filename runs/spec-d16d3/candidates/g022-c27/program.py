import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe fallback: incidence graph of PG(2, q), q the largest prime power with
# q + 1 <= d. Diameter 3, so valid for every D >= 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Different family for D = 3: Haar graphs H(Z_m, S) with |S| = d.
#
# Vertices a_i = i and b_j = m + j; a_i ~ b_j iff j - i in S.
# Bipartite, d-regular, order 2m. Diameter <= 3 holds iff
#   (same side)  every nonzero residue is a difference s1 - s2 (S - S covers Z_m \ {0}),
#   (cross side) every residue lies in S U (S - S + S).
# So the search is over difference-type sets, which is a very different
# structure from the projective-plane constructions and can exceed them.
# ----------------------------------------------------------------------------

def _cost(S, m):
    """Number of residues violating the same-side or cross-side reach condition. Zero means diameter <= 3."""
    arr = np.array(S, dtype=np.int64)
    diff = (arr[:, None] - arr[None, :]) % m
    cov = np.zeros(m, dtype=bool)
    cov[diff.ravel()] = True
    cov[0] = True
    tri = (arr[:, None, None] - arr[None, :, None] + arr[None, None, :]) % m
    cc = np.zeros(m, dtype=bool)
    cc[tri.ravel()] = True
    cc[arr] = True
    return (m - int(cov.sum())) + (m - int(cc.sum()))


def _search_m(d, m, rng, deadline):
    """Simulated annealing for a connection set S (|S| = d, 0 in S) in Z_m with cost 0; None on timeout."""
    if m < d + 1 or d * (d - 1) + 1 < m:
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)
        c = _cost(S, m)
        T = 0.6
        for it in range(30000):
            if c == 0:
                return S
            if (it & 63) == 0 and time.monotonic() >= deadline:
                return None
            i = rng.randrange(1, d)
            x = rng.randrange(1, m)
            if x in S:
                continue
            old = S[i]
            S[i] = x
            c2 = _cost(S, m)
            delta = c2 - c
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                c = c2
            else:
                S[i] = old
            if T > 0.15:
                T *= 0.9997
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Baseline valid graph: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass

    if D == 3:
        try:
            # Ascend through Haar moduli m; each success gives order 2m.
            target = max(d + 1, best_n // 2 + 1)
            upper = d * (d - 1) + 1
            while time.monotonic() < deadline and target <= upper:
                now = time.monotonic()
                remaining = deadline - now
                slice_end = min(deadline, now + max(1.5, 0.3 * remaining))
                S = _search_m(d, target, rng, slice_end)
                if S is not None:
                    n, e = lib.haar_graph(target, S)
                    consider(n, e)
                    target += 1
                # On failure the same target is retried with fresh random starts.
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
