"""Cyclic difference-cover Haar graphs for diameter 3 (bold change from the arc-extension family).

Construction: the Haar graph of Z_m with connection set S (|S| = d, 0 in S) has parts
A_i and B_j with A_i ~ B_{i+s} for s in S. Translation symmetry means distances from
A_0 and B_0 determine all distances. Diameter <= 3 holds whenever the difference set
S - S covers all of Z_m, since A_0 reaches A_x for x in S - S within 2 steps and every
B_y within 3 steps through (S - S) + S = Z_m. Order is 2m, so the target is m >= 198 for
d = 16 (order 396 > 394). A simulated-annealing search over S minimises the number of
uncovered differences, with O(d) incremental updates per move.

Safe fallbacks: K_{d,d} (diameter 2, optimal for D = 2) and the projective plane
incidence graph PG(2, q) with q the largest prime power <= d - 1 (diameter 3).
Every candidate is checked with lib.is_valid before it is kept.
"""
import math
import random
import time

import lib


def _fallback(d):
    """K_{d,d}: valid for every D >= 2 and d >= 1."""
    return lib.haar_graph(d, range(d))


def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _find_difference_cover(m, d, rng, deadline):
    """Find S in Z_m, |S| = d, 0 in S, with S - S = Z_m (then Haar(m, S) has diameter 3).

    Simulated annealing on the number of uncovered nonzero differences. The count
    cnt[x] is the number of ordered pairs (a, b) in S with a - b = x. Temperature decays
    geometrically over the time budget. Returns S, or None if the budget runs out.
    """
    if d > m or m > d * (d - 1) + 1:
        return None

    S = [0] + rng.sample(range(1, m), d - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True

    cnt = [0] * m
    unc = m - 1  # nonzero residues not yet covered
    for i in range(d):
        for j in range(d):
            if i != j:
                x = (S[i] - S[j]) % m
                if cnt[x] == 0:
                    unc -= 1
                cnt[x] += 1

    def rem(s, others):
        """Remove element s from the set; return the number of residues that became uncovered."""
        newly = 0
        for b in others:
            x = (s - b) % m
            cnt[x] -= 1
            if cnt[x] == 0:
                newly += 1
            x = (b - s) % m
            cnt[x] -= 1
            if cnt[x] == 0:
                newly += 1
        return newly

    def add(t, others):
        """Add element t to the set; return the number of residues that became covered."""
        filled = 0
        for b in others:
            x = (t - b) % m
            if cnt[x] == 0:
                filled += 1
            cnt[x] += 1
            x = (b - t) % m
            if cnt[x] == 0:
                filled += 1
            cnt[x] += 1
        return filled

    T0, T1 = 1.5, 0.15
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-3)
    T = T0
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t_start) / span)
        i = rng.randrange(1, d)
        s = S[i]
        others = S[:i] + S[i + 1:]
        t = rng.randrange(1, m)
        while inS[t]:
            t = rng.randrange(1, m)
        u = rem(s, others)
        z = add(t, others)
        delta = u - z
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = t
            inS[s] = False
            inS[t] = True
            unc += delta
        else:
            rem(t, others)
            add(s, others)
    return S if unc == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d)
    if D == 2:
        return best

    # D >= 3: start from the projective plane baseline when it is larger.
    pg = _pg_base(d)
    if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
        best = pg

    # Main search: cyclic Haar graphs with S - S = Z_m, climbing m upward.
    m = max(d, best[0] // 2 + 1)
    m_max = d * (d - 1) + 1
    while m <= m_max and time.monotonic() < deadline:
        budget_end = min(deadline, time.monotonic() + 3.0)
        S = _find_difference_cover(m, d, rng, budget_end)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d)
    return best
