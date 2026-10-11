import math
import random
import time

import numpy as np

import lib


def _uncovered(S, m):
    """Count residues not reached by the Haar-graph walk sums for D = 4.

    With S containing 0, the Haar graph on Z_m has every a-a and b-b pair within distance 4
    iff (S-S)+(S-S) covers Z_m (the a-side), and every a-b pair within distance 3 iff
    S union (S-S+S) covers Z_m (the b-side). The two sides are swapped by an automorphism,
    so this is an exact diameter test. The return value is the total number of uncovered
    residues, which is 0 iff the graph has diameter <= 4.
    """
    diff = np.unique(((S[:, None] - S[None, :]) % m).ravel())
    sums = ((diff[:, None] + diff[None, :]) % m).ravel()
    ca = np.zeros(m, dtype=bool)
    ca[sums] = True
    t = ((S[:, None, None] - S[None, :, None] + S[None, None, :]) % m).ravel()
    cb = np.zeros(m, dtype=bool)
    cb[t] = True
    cb[S] = True
    return int(m - np.count_nonzero(ca)) + int(m - np.count_nonzero(cb))


def _anneal(d, m, rng, end):
    """Simulated annealing over connection sets S (|S| = d, 0 in S) for Z_m until uncovered = 0."""
    if m < d:
        return None
    S_list = [0] + rng.sample(range(1, m), d - 1)
    cur = _uncovered(np.array(S_list, dtype=np.int64), m)
    T, stall = 1.0, 0
    while cur > 0:
        if time.monotonic() >= end:
            return None
        i = rng.randrange(1, d)
        inS = set(S_list)
        v = rng.randrange(1, m)
        while v in inS:
            v = rng.randrange(1, m)
        cand = S_list.copy()
        cand[i] = v
        c = _uncovered(np.array(cand, dtype=np.int64), m)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            if c < cur:
                stall = 0
            S_list, cur = cand, c
        else:
            stall += 1
        T = max(0.1, T * 0.9995)
        if stall > 4000:
            T, stall = 1.0, 0
    return S_list


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid

    if D != 4:
        # Generic fallback: random Haar graphs checked by the library.
        rng = random.Random(seed)
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

    # D = 4: binary search on the cyclic group order m, with annealing as the feasibility test.
    rng = random.Random(seed)
    lo = d                                   # feasible (K_{d,d})
    hi = lib.moore_bound(d, D) // 2 + 1      # Haar order 2m cannot exceed the Moore bound
    best_m, best_S = None, None
    while hi - lo > 1:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        mid = (lo + hi) // 2
        probe_end = min(deadline, now + max(0.5, 0.45 * remaining))
        S = _anneal(d, mid, rng, probe_end)
        if S is not None:
            lo, best_m, best_S = mid, mid, S
        else:
            hi = mid

    if best_S is not None:
        n, edges = lib.haar_graph(best_m, [int(s) for s in best_S])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return best
