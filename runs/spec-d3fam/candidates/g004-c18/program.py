"""Difference-cover Haar graphs for D = 3.

New idea: the Haar graph H(m, S) of the cyclic group Z_m (a_i ~ b_j iff j - i in S,
|S| = d) is bipartite, d-regular, and has diameter 3 exactly when the difference set
S - S covers all of Z_m. The search anneals a d-subset of Z_m that covers every
nonzero residue, and increases m while it keeps succeeding. Each hit gives a valid
graph on 2m vertices. The result is compared with the Araujo-Pardo-Lopez / PG / K_{d,d}
bases and the largest valid graph is returned.
"""
import math
import random
import time

import lib

TIME_FRAC = 0.85     # fraction of time_limit used before returning
MARGIN = 2.0         # seconds kept in reserve


# ---------------------------------------------------------------- base constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- difference covers

def _change(cnt, m, others, x, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between x and each
    element of `others` in the cover counter `cnt`. Returns the change in the number
    of uncovered nonzero residues."""
    dunc = 0
    for y in others:
        for r in ((x - y) % m, (y - x) % m):
            if sign > 0:
                if cnt[r] == 0:
                    dunc -= 1
                cnt[r] += 1
            else:
                cnt[r] -= 1
                if cnt[r] == 0:
                    dunc += 1
    return dunc


def _cover_set(k, m, rng, deadline, restart_iters=40000):
    """Anneal a k-subset S of Z_m with 0 in S so that S - S covers Z_m.
    Returns S, or None if the restart budget or deadline runs out."""
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    it = 0
    while unc > 0:
        it += 1
        if it > restart_iters:
            return None
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        idx = rng.randrange(1, k)
        old = S[idx]
        new = rng.randrange(1, m)
        if new in S:
            continue
        others = S[:idx] + S[idx + 1:]
        delta = _change(cnt, m, others, old, -1) + _change(cnt, m, others, new, 1)
        T = 0.5 * (1.0 - it / restart_iters) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = new
            unc += delta
        else:
            _change(cnt, m, others, new, -1)
            _change(cnt, m, others, old, 1)
    return S


def _search_cover(d, m, rng, deadline):
    """Increase m while a difference cover of size d is found. Returns the last
    valid (n, edges) found, or None."""
    best = None
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        budget = now + 0.6 * (deadline - now)
        S = None
        while S is None and time.monotonic() < budget:
            S = _cover_set(d, m, rng, budget)
        if S is None:
            break
        n, e = lib.haar_graph(m, S)
        if not lib.is_valid(n, e, d, 3):
            break
        best = (n, e)
        m += 1
    return best


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

    kdd = lib.haar_graph(d, range(d))
    cands = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    pg = _pg_base(d)
    if pg is not None:
        cands.append(pg)
    cands.append(kdd)

    valid = [(n, e) for n, e in cands if lib.is_valid(n, e, d, D)]
    if not valid:
        return kdd
    best_n, best_e = max(valid, key=lambda c: c[0])

    # New step: cyclic Haar graphs from difference covers, for D = 3.
    if D == 3 and time.monotonic() < deadline:
        m_start = max(best_n // 2 + 1, d)
        found = _search_cover(d, m_start, rng, deadline)
        if found is not None and found[0] > best_n and lib.is_valid(found[0], found[1], d, D):
            best_n, best_e = found

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return kdd
