import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: cyclic Haar graphs from covering difference sets.
#
# A Haar graph H(m, S) on Z_m has parts a_i, b_j with a_i ~ b_j iff j - i in S.
# It is bipartite and |S|-regular. Two a-vertices are at distance 2 exactly when
# their index difference lies in S - S, so diameter 3 needs S - S to cover all
# nonzero residues of Z_m. With |S| = k, this allows m up to k(k-1) + 1, giving
# order 2m up to the Moore bound. The search finds such sets S by simulated
# annealing and grows m until the search stalls.
#
# Fallbacks, all checked with lib.is_valid: K_{d,d}, and PG(2,q) incidence for
# the largest prime power q with q + 1 <= d.
# ----------------------------------------------------------------------------


def _shift(cnt, S, skip, v, m, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between v and
    every element of S except index `skip`. Returns the change in the number of
    residues in 1..m-1 with zero count."""
    dc = 0
    for j, s in enumerate(S):
        if j == skip:
            continue
        r1 = (v - s) % m
        r2 = (s - v) % m
        if sign > 0:
            if cnt[r1] == 0:
                dc -= 1
            cnt[r1] += 1
            if cnt[r2] == 0:
                dc -= 1
            cnt[r2] += 1
        else:
            cnt[r1] -= 1
            if cnt[r1] == 0:
                dc += 1
            cnt[r2] -= 1
            if cnt[r2] == 0:
                dc += 1
    return dc


def _init_state(m, k, rng):
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    cost = sum(1 for r in range(1, m) if cnt[r] == 0)
    return S, inS, cnt, cost


def _find_cover(m, k, rng, deadline):
    """Find S in Z_m with |S| = k, 0 in S, and S - S covering all nonzero residues.
    Returns the list S, or None if the deadline passes first."""
    if k < 2 or m < k + 1 or m - 1 > k * (k - 1):
        return None
    T = 0.35
    it = 0
    while True:
        if time.monotonic() > deadline:
            return None
        S, inS, cnt, cost = _init_state(m, k, rng)
        best = cost
        stale = 0
        while cost > 0:
            it += 1
            if (it & 4095) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(1, k)
            x = S[i]
            y = rng.randrange(1, m)
            if inS[y]:
                continue
            d1 = _shift(cnt, S, i, x, m, -1)
            S[i] = y
            d2 = _shift(cnt, S, i, y, m, 1)
            delta = d1 + d2
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                inS[x] = False
                inS[y] = True
                cost += delta
                if cost < best:
                    best = cost
                    stale = 0
                else:
                    stale += 1
            else:
                _shift(cnt, S, i, y, m, -1)
                S[i] = x
                _shift(cnt, S, i, x, m, 1)
                stale += 1
            if stale > 100000:
                break  # restart from a fresh random set
        if cost == 0:
            return list(S)


def _search_haar(k, rng, deadline):
    """Grow m upward while a covering set S of size k is found. Returns (m, S) or None."""
    best = None
    m = k + 1
    maxm = 1 + k * (k - 1)
    fails = 0
    while m <= maxm and time.monotonic() < deadline:
        budget = min(deadline, time.monotonic() + 3.0)
        S = _find_cover(m, k, rng, budget)
        if S is not None:
            best = (m, S)
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                break
        m += 1
    return best


def _pg_candidate(d):
    """Incidence graph of PG(2,q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = 2, [(0, 1)]

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D >= 3:
        # PG(2,q) incidence fallback (diameter 3, degree q+1 <= d).
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Main search: cyclic Haar graphs with covering difference sets.
        rng = random.Random(seed * 1000003 + d * 31 + D)
        found = _search_haar(d, rng, deadline)
        if found is not None:
            m, S = found
            n, E = lib.haar_graph(m, S)
            consider(n, E)

    return best_n, list(best_E)
