import math
import random
import time

import lib

TIME_FRAC = 0.85     # fraction of time_limit used before returning
MARGIN = 2.0         # seconds kept in reserve
ITER = 150000        # annealing moves per restart


# ---------------------------------------------------------------- fallbacks

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (degree q+1 <= d)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _best_fallback(d, D):
    """Largest valid known graph for (d, D) that is cheap to build."""
    kdd = lib.haar_graph(d, range(d))          # K_{d,d}: diameter 2, valid for D >= 2
    cands = [kdd]
    if D == 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        pg = _pg_base(d)
        if pg is not None:
            cands.append(pg)
    valid = [(n, e) for n, e in cands if lib.is_valid(n, e, d, D)]
    if not valid:
        return kdd
    return max(valid, key=lambda c: c[0])


# ---------------------------------------------------------------- Haar search
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S (|S| = d). It is bipartite and d-regular.
# It has diameter <= 3 exactly when S - S covers all of Z_m. Search for such S
# with m as large as possible, by annealing the number of uncovered residues.

def _anneal(m, d, rng, deadline):
    """Try to find S (|S| = d, 0 in S) with S - S = Z_m. Returns S or None."""
    S = [0] + rng.sample(range(1, m), d - 1)
    cnt = [0] * m
    for i in range(d):
        for j in range(d):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    if unc == 0:
        return S

    def move(i, b):
        """Replace S[i] by b, updating difference counts and uncovered count."""
        nonlocal unc
        a = S[i]
        for j in range(d):
            if j == i:
                continue
            x = (a - S[j]) % m
            cnt[x] -= 1
            if cnt[x] == 0:
                unc += 1
            x = (S[j] - a) % m
            cnt[x] -= 1
            if cnt[x] == 0:
                unc += 1
        S[i] = b
        for j in range(d):
            if j == i:
                continue
            x = (b - S[j]) % m
            if cnt[x] == 0:
                unc -= 1
            cnt[x] += 1
            x = (S[j] - b) % m
            if cnt[x] == 0:
                unc -= 1
            cnt[x] += 1

    for it in range(ITER):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, d)
        b = rng.randrange(1, m)
        if b in S:
            continue
        a = S[i]
        old = unc
        move(i, b)
        delta = unc - old
        temp = 0.6 * (1.0 - it / ITER) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            if unc == 0:
                return S
        else:
            move(i, a)
    return None


def _find_cover(m, d, rng, deadline):
    """Repeated annealing restarts until a covering set is found or time runs out."""
    while time.monotonic() < deadline:
        S = _anneal(m, d, rng, deadline)
        if S is not None:
            return S
    return None


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

    best_n, best_e = _best_fallback(d, D)
    if D != 3 or d < 3:
        return best_n, best_e

    # Haar-graph search: find m > best_n/2 with S - S = Z_m, |S| = d.
    m = best_n // 2 + 1
    while time.monotonic() < deadline:
        S = _find_cover(m, d, rng, deadline)
        if S is None:
            break
        n, e = lib.haar_graph(m, S)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
        m += 1

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return lib.haar_graph(d, range(d))
