"""Haar-graph (bi-Cayley) search for diameter-3 bipartite graphs.

For D = 3, the Haar graph H(m, S) on Z_m x {0,1} (a_i ~ b_{i+s}, s in S, |S| = d)
has diameter 3 exactly when
  (1) S - S covers all of Z_m (a-a and b-b distances <= 2), and
  (2) S union (S - S + S) covers all of Z_m (a-b distances <= 3).
Such graphs have 2m vertices, so any valid S with m >= record/2 + 1 beats the record.
The search anneals S over Z_m for growing m. Every output is checked with lib.is_valid,
and a verified parent-style base construction is the fallback.
"""
import math
import random
import time

import lib

TIME_FRAC = 0.80      # fraction of time_limit used before returning
MARGIN = 3.0          # seconds kept in reserve
STEPS = 150000        # annealing steps per attempt


# ---------------------------------------------------------------- fallback base

def _base(d, D):
    """Best verified parent-style base construction for (d, D)."""
    cands = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        cands.append(lib.projective_plane_incidence(d - 1))
    if D >= 3:
        q = d - 1
        while q >= 2 and not lib.is_prime_power(q):
            q -= 1
        if q >= 2 and q != d - 1:
            cands.append(lib.projective_plane_incidence(q))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    cands.append(lib.haar_graph(d, range(d)))  # K_{d,d}, diameter 2
    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    return max(valid, key=lambda c: c[0])


# ---------------------------------------------------------------- annealing

def _move(cnt, S, i, z, m, unc):
    """Replace S[i] by z, updating difference counts. Returns the new number of uncovered residues."""
    x = S[i]
    for j, y in enumerate(S):
        if j == i:
            continue
        for r in ((x - y) % m, (y - x) % m):
            cnt[r] -= 1
            if cnt[r] == 0:
                unc += 1
    for j, y in enumerate(S):
        if j == i:
            continue
        for r in ((z - y) % m, (y - z) % m):
            if cnt[r] == 0:
                unc -= 1
            cnt[r] += 1
    S[i] = z
    return unc


def _anneal(m, d, deadline, rng):
    """Search a d-subset S of Z_m with S - S covering Z_m (and S u (S-S+S) covering Z_m)."""
    S = rng.sample(range(m), d)
    cnt = [0] * m
    for i in range(d):
        for j in range(d):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)
    for it in range(STEPS):
        if unc == 0:
            break
        if it & 255 == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        z = rng.randrange(m)
        if z in S:
            continue
        old = S[i]
        temp = 0.6 * (1.0 - it / STEPS) + 0.05
        new_unc = _move(cnt, S, i, z, m, unc)
        delta = new_unc - unc
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            unc = new_unc
        else:
            _move(cnt, S, i, old, m, new_unc)
    if unc != 0:
        return None
    cov = set(S)
    for a in S:
        for b in S:
            for c in S:
                cov.add((a - b + c) % m)
    if len(cov) != m:
        return None
    return S


def _haar_search(d, m_start, deadline, rng):
    """Grow m while annealing succeeds. Returns the best verified (n, edges) found, or None."""
    best = None
    m = m_start
    m_max = d * d - d + 1  # Moore-type bound for the Haar graph order 2m
    while time.monotonic() < deadline and m <= m_max:
        S = _anneal(m, d, deadline, rng)
        if S is None:
            continue
        n, e = lib.haar_graph(m, S)
        if lib.is_valid(n, e, d, 3):
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
    if d == 2:  # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    base_n, base_e = _base(d, D)

    # Haar search only where the projective plane is not already Moore-extremal.
    if D == 3 and d >= 3 and not lib.is_prime_power(d - 1):
        try:
            m_start = max(base_n // 2 + 1, d + 1)
            res = _haar_search(d, m_start, deadline, rng)
            if res is not None and res[0] > base_n and lib.is_valid(res[0], res[1], d, D):
                return res
        except Exception:
            pass

    return base_n, base_e
