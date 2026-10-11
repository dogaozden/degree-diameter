import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cyclic Haar-type lifts (bipartite, degree d) searched directly for diameter D.
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, |S| = d. It is bipartite and
# d-regular. Walks of length 2j between a-vertices reach differences in
# L_j = (S-S)+...+(S-S) (j terms). Walks of length 2j+1 from a_0 to b-vertices
# reach S + L_j. So diameter <= D holds iff L_{floor(D/2)} = Z_m and
# S + L_{floor((D-1)/2)} = Z_m. We anneal S (with 0 in S, WLOG) to cover Z_m.
# ----------------------------------------------------------------------------

def _rot(mask, s, m, full):
    """Cyclic shift of an m-bit set mask by s (element x goes to x+s mod m)."""
    s %= m
    if s == 0:
        return mask
    return ((mask << s) | (mask >> (m - s))) & full


def _bits(mask):
    out = []
    while mask:
        low = mask & -mask
        out.append(low.bit_length() - 1)
        mask ^= low
    return out


def _sumset(A, elems, m, full):
    r = 0
    for b in elems:
        r |= _rot(A, b, m, full)
    return r


def _cost(m, full, D, S):
    """Number of uncovered residues (a-a even distances and a-b odd distances) for Haar(m, S)."""
    Sm = 0
    for s in S:
        Sm |= 1 << s
    D1m = 0
    for s in S:
        D1m |= _rot(Sm, -s, m, full)
    D1 = _bits(D1m)
    lv = [1]
    for _ in range(D // 2):
        lv.append(_sumset(lv[-1], D1, m, full))
    even = lv[D // 2]
    odd = _sumset(Sm, _bits(lv[(D - 1) // 2]), m, full)
    return (m - even.bit_count()) + (m - odd.bit_count())


def _search(m, d, D, deadline, rng):
    """Anneal a size-d connection set S in Z_m (containing 0) with zero cost. Returns sorted S or None."""
    if d < 2 or m < d:
        return None
    full = (1 << m) - 1
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)
        cur = _cost(m, full, D, S)
        stall = 0
        while cur > 0 and stall < 2000:
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(1, d)
            v = rng.randrange(1, m)
            if v in S:
                stall += 1
                continue
            old = S[i]
            S[i] = v
            c = _cost(m, full, D, S)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / 0.6):
                cur = c
                stall = 0 if delta < 0 else stall + 1
            else:
                S[i] = old
                stall += 1
        if cur == 0:
            return sorted(S)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact optimum for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))

    # Already at the Moore bound: nothing to gain.
    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Bipartite graphs with |V| = 2m need m <= moore / 2.
    moore_half = moore // 2
    m = max(d, best[0] // 2 + 1)
    while m <= moore_half and time.monotonic() < deadline - 0.5:
        remaining = deadline - time.monotonic()
        slice_end = time.monotonic() + min(remaining, 8.0)
        S = _search(m, d, D, slice_end, rng)
        if S is None:
            break
        n2, e2 = lib.haar_graph(m, S)
        consider(n2, e2)
        m += 1

    return best
