import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines (cheap, deterministic):
#   * Araujo-Pardo & Lopez graph for d = q + 2 with q a prime power (diameter 3).
#   * Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d.
#   * K_{d,d} fallback (diameter 2, valid for any D >= 2).
#
# Haar-graph search (D = 3):
#   H(Z_m, S) with |S| = d has diameter 3 iff S - S covers Z_m. Its order is 2m,
#   so beating a baseline of order N only needs m >= N/2 + 1. The search
#   therefore starts at the smallest m that would beat the current best and
#   climbs by one each time a difference cover is found. Each annealing call
#   is a bounded chunk with a fresh random start, so a stuck run is restarted
#   instead of wasting the remaining budget.
# ----------------------------------------------------------------------------


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _dc_apply(cnt, S, skip, v, m, sign):
    """Add (sign=+1) or remove (sign=-1) the differences of value v against S[j], j != skip.

    Returns the change in the number of uncovered nonzero residues.
    """
    change = 0
    for j, b in enumerate(S):
        if j == skip:
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


def _dc_anneal(d, m, rng, deadline):
    """Find S, |S| = d, containing 0, in Z_m with S - S = Z_m; None on failure or timeout."""
    if m < d or m - 1 > d * (d - 1):
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    cnt = [0] * m
    unc = m - 1
    for j in range(d):
        for k in range(j + 1, d):
            for y in ((S[j] - S[k]) % m, (S[k] - S[j]) % m):
                if cnt[y] == 0:
                    unc -= 1
                cnt[y] += 1
    if unc == 0:
        return S

    start = time.monotonic()
    span = max(1e-6, deadline - start)
    frac = 0.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 127) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = (now - start) / span
        T = 1.0 * (0.02 ** frac)
        idx = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[idx]
        delta = _dc_apply(cnt, S, idx, old, m, -1) + _dc_apply(cnt, S, idx, x, m, +1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = x
            unc += delta
        else:
            _dc_apply(cnt, S, idx, x, m, -1)
            _dc_apply(cnt, S, idx, old, m, +1)
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Algebraic baselines.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Haar search aimed strictly above the current best order.
        max_m = d * (d - 1) + 1
        m = max(d, best_n // 2 + 1)
        chunk = max(1.0, 0.15 * time_limit)
        while m <= max_m and time.monotonic() < deadline:
            rem = deadline - time.monotonic()
            S = _dc_anneal(d, m, rng, time.monotonic() + min(rem, chunk))
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
                # Found a cover at m: the next candidate must beat 2m.
                m = max(m + 1, best_n // 2 + 1)
            # On failure, retry the same m with a fresh random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
