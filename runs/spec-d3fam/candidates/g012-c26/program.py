import math
import random
import time

import lib

TIME_FRAC = 0.80     # fraction of time_limit used before returning
MARGIN = 3.0         # seconds kept in reserve
STEPS = 4000         # annealing steps per restart


# ---------------------------------------------------------------- base constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- cyclic Haar search (D = 3)
#
# Haar graph H(Z_m, S): a_i ~ b_{i+s} for s in S, |S| = d, 0 in S (WLOG).
# It is bipartite and d-regular on 2m vertices. Using the vertex-transitivity of each
# side and the side-swapping automorphism a_i -> b_{-i}, diameter <= 3 holds iff
#   (S - S) covers all of Z_m          (A-A pairs at distance <= 2)
#   (S - S) + S covers all of Z_m      (A-B pairs at distance <= 3)
# The cost below counts the uncovered residues of both conditions.

def _cost(m, S):
    diffs = {(s - t) % m for s in S for t in S}          # contains 0
    reach = {(x + u) % m for x in diffs for u in S}      # contains S
    return (m - len(diffs)) + (m - len(reach))


def _anneal(m, d, rng, deadline, steps):
    """Search a d-subset of Z_m (containing 0) with zero cost. Returns it or None."""
    S = [0] + rng.sample(range(1, m), d - 1)
    cost = _cost(m, S)
    for it in range(steps):
        if cost == 0:
            return S
        if (it & 63) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, d)
        c = rng.randrange(1, m)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        new = _cost(m, S)
        temp = 1.0 * (1.0 - it / steps) + 0.05
        if new <= cost or rng.random() < math.exp(-(new - cost) / temp):
            cost = new
        else:
            S[i] = old
    return S if cost == 0 else None


def _haar_search(d, D, lower, rng, deadline):
    """Find the largest m >= lower for which a diameter-3 Haar graph is found. Returns (n, edges) or None."""
    best = None
    m = lower
    # Necessary: m <= d(d-1)+1 (count of difference slots).
    while m <= d * (d - 1) + 1 and time.monotonic() < deadline:
        now = time.monotonic()
        m_deadline = min(deadline, now + max(3.0, 0.6 * (deadline - now)))
        S = None
        while S is None and time.monotonic() < m_deadline:
            S = _anneal(m, d, rng, m_deadline, STEPS)
        if S is None:
            break
        n, edges = lib.haar_graph(m, S)
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            m += 1
        else:
            break
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # K_{d,d} has diameter 2, so it is a safe fallback for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    if D > 3:
        return fallback

    # D == 3 from here on.
    if lib.is_prime_power(d - 1):    # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    cands = []
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))  # record construction, degree d
        except Exception:
            pass
    pg = _pg_base(d)
    if pg is not None:
        cands.append(pg)
    cands.append(fallback)

    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    if not valid:
        return fallback
    best_n, best_e = max(valid, key=lambda c: c[0])

    # Bold alternative: cyclic Haar graphs found by annealing over difference covers.
    # Start just above half the current best order so the search aims to beat it.
    res = _haar_search(d, D, best_n // 2 + 1, rng, deadline)
    if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
        return res

    return best_n, best_e
