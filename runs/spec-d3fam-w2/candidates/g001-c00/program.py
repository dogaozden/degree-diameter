import math
import random
import time

import lib

TIME_FRAC = 0.85     # fraction of time_limit used before returning
MARGIN = 2.0         # seconds kept in reserve
ITERS = 30000        # annealing steps per attempt at a fixed modulus m


# ---------------------------------------------------------------- difference covers
#
# New routine: a Haar graph H(m, S) on Z_m with |S| = d is d-regular bipartite.
# Its vertices a_i and b_j are at distance <= 3 for all pairs iff
#   S - S = Z_m   (even distances between same-side vertices), and
#   S + (S - S) covers Z_m (odd distances between opposite sides),
# and the second condition follows from the first.  So a difference cover of
# Z_m by d elements (with 0 in S, WLOG) gives a valid diameter-3 graph on 2m
# vertices.  We search for such covers by simulated annealing over S, using
# bitmasks for the difference sets.

def _rot(x, t, m, full):
    """Return the bitmask with bit (s - t) mod m set for every set bit s of x."""
    t %= m
    if t == 0:
        return x
    return ((x >> t) | (x << (m - t))) & full


def _uncovered(smask, S, m, full):
    """Number of residues in Z_m not of the form s - t with s, t in S."""
    cov = 0
    for t in S:
        cov |= _rot(smask, t, m, full)
    return m - cov.bit_count()


def _find_cover(m, k, rng, deadline, iters):
    """Anneal a k-subset S of Z_m (containing 0) with S - S = Z_m. Return S or None."""
    if m < k or k < 2:
        return None
    full = (1 << m) - 1
    S = [0] + rng.sample(range(1, m), k - 1)
    smask = 0
    for s in S:
        smask |= 1 << s
    cost = _uncovered(smask, S, m, full)
    for it in range(iters):
        if cost == 0:
            return S
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, k)
        v = rng.randrange(1, m)
        if v in S:
            continue
        old = S[i]
        S[i] = v
        nmask = (smask & ~(1 << old)) | (1 << v)
        new = _uncovered(nmask, S, m, full)
        delta = new - cost
        temp = 1.0 * (1.0 - it / iters) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            smask = nmask
            cost = new
        else:
            S[i] = old
    return S if cost == 0 else None


def _haar_search(d, D, rng, deadline):
    """Grow m upward; at each m find a difference cover and keep the largest valid Haar graph."""
    best = None
    m_cap = min(d * (d - 1) + 1, lib.moore_bound(d, D) // 2)
    m = d
    while m <= m_cap and time.monotonic() < deadline:
        S = _find_cover(m, d, rng, deadline, ITERS)
        if S is None:
            continue                      # retry the same m from a fresh start
        n, edges = lib.haar_graph(m, S)
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
        m += 1
    return best


# ---------------------------------------------------------------- bases

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                                   # even cycle of length 2D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    kdd = lib.haar_graph(d, range(d))            # K_{d,d}: diameter 2
    if D == 2:
        return kdd
    if D != 3:
        return kdd if lib.is_valid(kdd[0], kdd[1], d, D) else kdd

    # D == 3 from here on.
    if lib.is_prime_power(d - 1):                # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    cands = [kdd]
    pg = _pg_base(d)
    if pg is not None:
        cands.append(pg)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    cands = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    best_n, best_e = max(cands, key=lambda c: c[0])

    found = _haar_search(d, D, rng, deadline)
    if found is not None and found[0] > best_n:
        best_n, best_e = found

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return kdd
