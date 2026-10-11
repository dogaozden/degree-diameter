import math
import random
import time

import lib

TIME_FRAC = 0.80      # fraction of time_limit used before returning
MARGIN = 1.0          # seconds kept in reserve
RUN_LEN = 60000       # annealing moves per restart of a difference-cover search
T_HI = 1.0
T_LO = 0.03


# ---------------------------------------------------------------- base constructions

def _pg_base(d):
    """Incidence graph of PG(2, q), q the largest prime power <= d-1 (degree q+1 <= d)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- difference covers

def _apply(cnt, S, idx, v, m, sign):
    """Add (sign=+1) or remove (sign=-1) the differences between value v and every S[j], j != idx.

    Returns the change in the number of uncovered nonzero residues.
    """
    change = 0
    for j, b in enumerate(S):
        if j == idx:
            continue
        for y in ((v - b) % m, (b - v) % m):
            if sign > 0:
                if cnt[y] == 0:
                    change -= 1
                cnt[y] += 1
            else:
                cnt[y] -= 1
                if cnt[y] == 0:
                    change += 1
    return change


def _init(S, m):
    """Difference counts and number of uncovered nonzero residues for the set S."""
    cnt = [0] * m
    unc = m - 1
    d = len(S)
    for j in range(d):
        for k in range(j + 1, d):
            for y in ((S[j] - S[k]) % m, (S[k] - S[j]) % m):
                if cnt[y] == 0:
                    unc -= 1
                cnt[y] += 1
    return cnt, unc


def _dc_search(d, m, rng, deadline):
    """Find S of size d in Z_m with S - S = Z_m (so the Haar graph has diameter 3).

    Returns a sorted list or None if the deadline passes first. Restarts annealing
    from fresh random sets until success or timeout.
    """
    if m < d or m - 1 > d * (d - 1):
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)   # 0 WLOG: translation gives an isomorphic graph
        cnt, unc = _init(S, m)
        for it in range(RUN_LEN):
            if unc == 0:
                return sorted(S)
            if (it & 1023) == 0 and time.monotonic() >= deadline:
                return None
            T = T_HI * (T_LO / T_HI) ** (it / RUN_LEN)
            idx = rng.randrange(1, d)
            x = rng.randrange(1, m)
            if x in S:
                continue
            old = S[idx]
            delta = _apply(cnt, S, idx, old, m, -1) + _apply(cnt, S, idx, x, m, 1)
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S[idx] = x
                unc += delta
            else:
                _apply(cnt, S, idx, x, m, -1)
                _apply(cnt, S, idx, old, m, 1)
        if unc == 0:
            return sorted(S)
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                      # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    kdd = lib.haar_graph(d, range(d))   # K_{d,d}: diameter 2, valid for any D >= 2
    if D == 2:
        return kdd

    # D >= 3 from here on. Diameter-3 constructions are also valid for any D >= 3.
    if lib.is_prime_power(d - 1):       # Moore-optimal projective plane
        pg = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(pg[0], pg[1], d, D):
            return pg

    best = kdd
    cands = []
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))   # record family, degree q+2 = d
        except Exception:
            pass
    pg = _pg_base(d)
    if pg is not None:
        cands.append(pg)
    for n, e in cands:
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Haar graph search: order 2m beats the current best once m > best_n / 2.
    # Feasibility only gets harder as m grows, so push m up from the first target.
    best_n = best[0]
    max_m = d * (d - 1) + 1
    m = max(d, best_n // 2 + 1)
    while m <= max_m and time.monotonic() < deadline:
        S = _dc_search(d, m, rng, deadline)
        if S is None:
            break
        n, e = lib.haar_graph(m, S)
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
        m += 1

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return kdd
