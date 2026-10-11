import math
import random
import time

import lib

TIME_FRAC = 0.85      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
SLICE_FRAC = 0.4      # share of remaining search time given to one circulant size
T0 = 3.0              # starting annealing temperature (in bad-pair units)
PERIOD = 4000         # annealing reheat period (iterations)


# ---------------------------------------------------------------- baselines

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (None if none)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _baseline(d, D):
    """Best valid baseline graph among the known constructions (always returns something valid)."""
    cands = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 3:
        pg = _pg_base(d)
        if pg is not None:
            cands.append(pg)
    cands.append(lib.haar_graph(d, range(d)))  # K_{d,d}, valid for D >= 2
    best = None
    for n, e in cands:
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)
    return best


# ---------------------------------------------------------------- circulant Haar search
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, S a subset of Z_m with |S| = d.
# It is bipartite and d-regular. By translation symmetry, diameter <= D holds iff
# every vertex is within distance D of a_0 and of b_0. The cost below counts the
# vertices NOT reached within D steps from those two sources (0 means valid).

def _rot(X, s, m, full):
    """Cyclically shift an m-bit set X by s (element i -> i + s mod m)."""
    if s == 0:
        return X
    return ((X << s) | (X >> (m - s))) & full


def _haar_cost(m, S, D, full):
    neg = [(m - s) % m for s in S]
    total = 0
    for src in (0, 1):
        if src == 0:
            rA, fA, rB, fB = 1, 1, 0, 0
        else:
            rA, fA, rB, fB = 0, 0, 1, 1
        for _ in range(D):
            nB = 0
            for s in S:
                nB |= _rot(fA, s, m, full)
            nA = 0
            for s in neg:
                nA |= _rot(fB, s, m, full)
            nB &= ~rB
            nA &= ~rA
            rB |= nB
            rA |= nA
            fA, fB = nA, nB
            if not fA and not fB:
                break
        total += 2 * m - rA.bit_count() - rB.bit_count()
    return total


def _search_haar(m, d, D, rng, deadline):
    """Anneal a d-subset S of Z_m (containing 0) so that H(m, S) has diameter <= D. Returns S or None."""
    full = (1 << m) - 1
    S = [0] + rng.sample(range(1, m), d - 1)
    cost = _haar_cost(m, S, D, full)
    it = 0
    while cost > 0:
        if it % 64 == 0 and time.monotonic() > deadline:
            return None
        it += 1
        temp = T0 * (1.0 - (it % PERIOD) / PERIOD) + 0.03
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c = _haar_cost(m, S, D, full)
        if c <= cost or rng.random() < math.exp(-(c - cost) / temp):
            cost = c
        else:
            S[i] = old
    return S


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                       # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    base = _baseline(d, D)
    if base is None:
        return lib.haar_graph(d, range(d))
    best_n, best_e = base

    # Bold alternative: circulant Haar graphs H(m, S) with |S| = d, searched by annealing.
    # Order is 2m, so we aim for m above the baseline's half-order.
    moore = lib._moore_bound(d, D)
    lo = best_n // 2 + 1
    hi = moore // 2
    m = lo
    while m <= hi and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        slice_end = min(deadline, time.monotonic() + max(1.0, SLICE_FRAC * remaining))
        if m < d + 1:
            m += 1
            continue
        S = _search_haar(m, d, D, rng, slice_end)
        if S is None:
            break                    # harder sizes are unlikely to succeed; stop here
        n, e = lib.haar_graph(m, S)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
        m += 1

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base
