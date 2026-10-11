import math
import random
import time

import lib

TIME_FRAC = 0.85     # fraction of time_limit used before returning
MARGIN = 2.0         # seconds kept in reserve


# ---------------------------------------------------------------- difference-cover search
#
# A bipartite Haar graph H(m, S) on Z_m x {A, B} joins a_i to b_{i+s} for s in S.
# It has order 2m, degree |S| = d, and diameter <= 3 exactly when the difference
# set S - S covers all of Z_m. This family is a different construction from the
# arc extensions of PG(2, q): it reaches orders up to 2(d(d-1)+1).

def _cover_search(m, d, deadline, rng):
    """Find S subset of Z_m with |S| = d and S - S = Z_m, by simulated annealing.

    Returns the list S, or None if the deadline passes first.
    """
    cur = rng.sample(range(m), d)
    cnt = [0] * m
    st = [m - 1]                       # st[0] = number of nonzero differences still uncovered
    for a in cur:
        for b in cur:
            if a != b:
                k = (a - b) % m
                if cnt[k] == 0:
                    st[0] -= 1
                cnt[k] += 1

    def rem_pair(x, others):
        for t in others:
            k = (x - t) % m
            cnt[k] -= 1
            if cnt[k] == 0:
                st[0] += 1
            k = (t - x) % m
            cnt[k] -= 1
            if cnt[k] == 0:
                st[0] += 1

    def add_pair(x, others):
        for t in others:
            k = (x - t) % m
            if cnt[k] == 0:
                st[0] -= 1
            cnt[k] += 1
            k = (t - x) % m
            if cnt[k] == 0:
                st[0] -= 1
            cnt[k] += 1

    it = 0
    while True:
        if st[0] == 0:
            return cur
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        it += 1
        idx = rng.randrange(d)
        old = cur[idx]
        new = rng.randrange(m)
        if new in cur:
            continue
        others = cur[:idx] + cur[idx + 1:]
        before = st[0]
        rem_pair(old, others)
        add_pair(new, others)
        delta = st[0] - before
        temp = 0.6 * (1.0 - (it % 40000) / 40000.0) + 0.04
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur[idx] = new
        else:
            rem_pair(new, others)
            add_pair(old, others)


# ---------------------------------------------------------------- known constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (degree q+1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree q+2 = d) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    usable = max(0.5, TIME_FRAC * time_limit - MARGIN)
    deadline = start + usable
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Moore-extremal projective plane (diameter 3, valid for D >= 3).
    if lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    pg = _pg_base(d)
    if pg is not None:
        consider(*pg)

    ar = _araujo(d)
    if ar is not None:
        consider(*ar)

    # Bold path: Haar graphs from difference covers, searched upward in m.
    # Each success gives a valid graph of order 2m, so we keep the largest.
    max_m = d * (d - 1) + 1
    m = max(d, best_n // 2 + 1)
    fails = 0
    while m <= max_m and fails < 2:
        rem = deadline - time.monotonic()
        if rem < 0.5:
            break
        budget = min(rem, max(1.5, 0.2 * usable))
        S = _cover_search(m, d, time.monotonic() + budget, rng)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            before = best_n
            consider(n, e)
            fails = 0 if best_n > before or True else fails
        else:
            fails += 1
        m += 1

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return fallback
