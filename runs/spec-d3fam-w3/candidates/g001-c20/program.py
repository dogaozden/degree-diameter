import math
import random
import time

import lib

TIME_FRAC = 0.80     # fraction of time_limit to use
MARGIN = 3.0         # seconds kept in reserve
REHEAT = 30000       # annealing schedule length before reheating


# ---------------------------------------------------------------- known constructions

def _pg_moore(d):
    """Moore-extremal incidence graph of PG(2, d-1), when d-1 is a prime power."""
    if lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree d) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


# ---------------------------------------------------------------- difference-cover Haar graphs
#
# A Haar graph H(m, S) on Z_m with |S| = d is d-regular and bipartite with 2m vertices.
# Two same-side vertices a_i, a_j are at distance 2 exactly when j - i lies in S - S, and
# opposite-side vertices are at distance <= 3 when every residue lies in S - S + S.
# So H(m, S) has diameter 3 whenever S - S covers all of Z_m. The search below looks for
# such a difference cover S of size d by simulated annealing on the number of uncovered
# nonzero residues, which gives order 2m for m up to about d^2 - d + 1.

def _upd(cnt, x, others, m, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between x and each element of others.

    Returns the change in the number of uncovered residues.
    """
    ch = 0
    for y in others:
        for t in ((x - y) % m, (y - x) % m):
            if sign < 0:
                cnt[t] -= 1
                if cnt[t] == 0:
                    ch += 1
            else:
                if cnt[t] == 0:
                    ch -= 1
                cnt[t] += 1
    return ch


def _difference_cover(m, d, rng, deadline):
    """Find S subset of Z_m with 0 in S, |S| = d and S - S = Z_m, or return None at the deadline."""
    if d > m:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = [False] * m
    for x in S:
        inS[x] = True
    cnt = [0] * m
    for i, x in enumerate(S):
        for j, y in enumerate(S):
            if i != j:
                cnt[(x - y) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    it = 0
    while unc > 0:
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        it += 1
        phase = (it % REHEAT) / REHEAT
        T = 0.6 * (1.0 - phase) + 0.03
        k = rng.randrange(1, d)            # S[0] = 0 stays fixed (translation invariance)
        old = S[k]
        others = S[:k] + S[k + 1:]
        new = -1
        if rng.random() < 0.6:
            # Targeted move: aim at a random uncovered difference u via new = y + u.
            for _ in range(30):
                u = rng.randrange(1, m)
                if cnt[u] == 0:
                    new = (rng.choice(others) + u) % m
                    break
        if new < 0:
            new = rng.randrange(1, m)
        if inS[new]:
            continue
        ch = _upd(cnt, old, others, m, -1)
        ch += _upd(cnt, new, others, m, +1)
        if ch <= 0 or rng.random() < math.exp(-ch / T):
            unc += ch
            inS[old] = False
            inS[new] = True
            S[k] = new
        else:
            _upd(cnt, new, others, m, -1)
            _upd(cnt, old, others, m, +1)
    return S


def _haar_search(d, deadline, rng):
    """Ascend over m, each time seeking a difference cover; return the largest valid (2m, edges) found."""
    upper = min(d * d - d + 1, lib.moore_bound(d, 3) // 2)
    lo = max(d + 1, (upper * 3) // 4)
    best = None
    fails = 0
    m = lo
    while m <= upper and time.monotonic() < deadline and fails < 3:
        remaining = deadline - time.monotonic()
        budget = max(0.5, 0.25 * remaining)
        S = _difference_cover(m, d, rng, min(deadline, time.monotonic() + budget))
        if S is None:
            fails += 1
        else:
            fails = 0
            n, e = lib.haar_graph(m, S)
            if len(set(S)) == d and lib.is_valid(n, e, d, 3):
                best = (n, e)
        m += 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    usable = min(TIME_FRAC * time_limit, time_limit - MARGIN)
    deadline = start + max(0.5, usable)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D is bipartite with diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                       # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3:
        pg = _pg_moore(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            return pg

    cands = [lib.haar_graph(d, range(d))]          # K_{d,d}, always valid for D >= 2
    if D >= 3:
        rec = _araujo(d)
        if rec is not None:
            cands.append(rec)
        pg = _pg_moore(d) if d >= 3 else None
        if pg is not None:
            cands.append(pg)
    if D == 3:
        h = _haar_search(d, deadline, rng)
        if h is not None:
            cands.append(h)

    valid = [(n, e) for n, e in cands if lib.is_valid(n, e, d, D)]
    if not valid:
        return lib.haar_graph(d, range(d))
    return max(valid, key=lambda c: c[0])
