import math
import random
import time

import lib

TIME_FRAC = 0.80      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
RESTART_ITERS = 4000  # annealing moves per random restart


# ---------------------------------------------------------------- baselines

def _safe(n, e, d, D):
    """Return (n, e) if it is valid for (d, D), else None."""
    try:
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return None


def _base(d, D):
    """Best verified construction from the existing pipeline. Always returns a valid graph."""
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    cands = []
    if D == 2:
        cands.append(lib.haar_graph(d, range(d)))             # K_{d,d}, diameter 2
    if D == 3:
        if lib.is_prime_power(d - 1):
            cands.append(lib.projective_plane_incidence(d - 1))  # Moore-extremal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))      # record construction
            except Exception:
                pass
        q = d - 1
        while q >= 2 and not lib.is_prime_power(q):
            q -= 1
        if q >= 2:
            cands.append(lib.projective_plane_incidence(q))
    cands.append(lib.haar_graph(d, range(d)))                 # K_{d,d}, diameter 2 <= D
    best = None
    for n, e in cands:
        ok = _safe(n, e, d, D)
        if ok and (best is None or ok[0] > best[0]):
            best = ok
    if best is None:
        best = _safe(*lib.haar_graph(d, range(d)), d, D)
    return best


# ------------------------------------------------- new construction: difference covers
#
# Haar graph H(Z_m, S) with |S| = d is bipartite and d-regular on 2m vertices.
# If S - S = Z_m (S is a difference cover of Z_m), every same-side pair is at
# distance <= 2 and every cross pair at distance <= 3, so diameter is 3.
# This is a different family from the cyclic growth/annealing approach of the
# parent: we search directly for small difference covers at large m.

def _cover_cost(S, m):
    """Number of residues r in Z_m not expressible as a difference of two elements of S."""
    seen = [False] * m
    seen[0] = True
    for a in S:
        for b in S:
            if a != b:
                seen[(a - b) % m] = True
    return seen.count(False)


def _find_cover(m, d, rng, deadline):
    """Simulated annealing for a d-subset S of Z_m (containing 0) with S - S = Z_m."""
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)
        cost = _cover_cost(S, m)
        for it in range(RESTART_ITERS):
            if cost == 0:
                return S
            if (it & 127) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(1, d)
            z = rng.randrange(1, m)
            if z in S:
                continue
            old = S[i]
            S[i] = z
            new = _cover_cost(S, m)
            T = 1.0 * (1.0 - it / RESTART_ITERS) + 0.02
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                S[i] = old
        if cost == 0:
            return S
    return None


def _search_haar(d, m_lo, deadline, rng):
    """Increase m from m_lo+1 while a difference cover of size d can be found. Returns best valid (n, e) or None."""
    best = None
    m = max(m_lo + 1, d)
    m_hi = d * d - d + 1          # counting bound: |S - S| <= d(d-1) + 1
    while m <= m_hi and time.monotonic() < deadline:
        now = time.monotonic()
        cap = now + max(2.0, 0.5 * (deadline - now))
        S = _find_cover(m, d, rng, min(deadline, cap))
        if S is None:
            break
        n, e = lib.haar_graph(m, S)
        ok = _safe(n, e, d, 3)
        if ok is None:
            break
        best = ok
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

    base = _base(d, D)
    if base is None:
        return 2, [(0, 1)] if d >= 1 and D >= 1 else (1, [])

    if D == 3 and d >= 3:
        try:
            found = _search_haar(d, base[0] // 2, deadline, rng)
        except Exception:
            found = None
        if found is not None and found[0] > base[0]:
            return found

    return base
