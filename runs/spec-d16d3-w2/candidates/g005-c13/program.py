import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction A (D <= 3 family): Haar graphs from difference covers.
#
# H(m, S) has parts A = Z_m and B = Z_m with a_i ~ b_{i+s} for s in S, |S| = d.
# A-A distances are <= 2 exactly when S - S covers Z_m. With S - S = Z_m the
# whole graph has diameter 3, and the order is 2m. We anneal S (with 0 fixed in
# S, since translating S gives an isomorphic graph) to minimise the number of
# uncovered nonzero differences, and grow m while covers keep being found.
# ----------------------------------------------------------------------------

def _anneal_cover(k, m, rng, deadline):
    """Find S in Z_m, |S| = k, 0 in S, with S - S = Z_m. Returns sorted S or None."""
    if m < k:
        return None
    if m == k:
        return list(range(m))
    S = [0] + rng.sample(range(1, m), k - 1)
    in_s = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 1.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 400000 == 0:
            T = 1.0
        T = max(0.15, T * 0.99995)
        i = rng.randrange(1, k)          # S[0] = 0 stays fixed
        x = S[i]
        y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        for s in others:                  # remove x's ordered differences
            for g in ((x - s) % m, (s - x) % m):
                cnt[g] -= 1
                if cnt[g] == 0:
                    delta += 1
        for s in others:                  # add y's ordered differences
            for g in ((y - s) % m, (s - y) % m):
                if cnt[g] == 0:
                    delta -= 1
                cnt[g] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            for s in others:              # undo the y additions
                for g in ((y - s) % m, (s - y) % m):
                    cnt[g] -= 1
            for s in others:              # restore the x differences
                for g in ((x - s) % m, (s - x) % m):
                    cnt[g] += 1
    return sorted(S)


def _haar_grow(k, rng, deadline):
    """Grow m upward from a high start; return (m, S) for the largest m with a cover found, or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    m = max(k, int(0.75 * mmax))
    best = None
    while m <= mmax and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        S = _anneal_cover(k, m, rng, time.monotonic() + max(0.5, 0.5 * remaining))
        if S is None:
            remaining = deadline - time.monotonic()
            if remaining <= 0.2:
                break
            S = _anneal_cover(k, m, rng, deadline)
            if S is None:
                break
        best = (m, S)
        m += 1
    return best


# ----------------------------------------------------------------------------
# Construction B (fallback for D >= 3): incidence graph of PG(2, q) with the
# largest prime power q <= d-1. Degree q+1 <= d, diameter 3.
# ----------------------------------------------------------------------------

def _projective_fallback(d):
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * float(time_limit), 46.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if D <= 0 or d <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D >= 3:
        # Cheap, certain improvement: projective plane incidence graph.
        if d >= 3:
            pg = _projective_fallback(d)
            if pg is not None:
                consider(pg[0], pg[1])

        # Bold path: difference-cover Haar graph, annealed and grown in m.
        if d >= 2 and time.monotonic() < deadline:
            res = _haar_grow(d, rng, deadline)
            if res is not None:
                m, S = res
                n, E = lib.haar_graph(m, S)
                consider(n, E)

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
