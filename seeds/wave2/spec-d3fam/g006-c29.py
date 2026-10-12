import math
import random
import time
import itertools

import lib


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph (diameter 3, degree q+1 <= d).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family for D >= 3: Haar graphs H(Z_m, S) with |S| = d.
#
# Vertices a_i and b_j (i, j in Z_m); a_i ~ b_{i+s} for s in S.
# Same-side distance is 2 exactly when the difference set S - S covers Z_m,
# and cross-side distance is then at most 3 (since S - S = Z_m implies
# every residue y = (y - u) + u with u in S). So diameter 3 holds iff S is a
# "difference cover" of Z_m. Any such S with m > d(d-1)/2 + ... gives order
# 2m, and the upper limit is m <= d(d-1) + 1.
#
# We search for S by simulated annealing, minimising the number of uncovered
# nonzero residues. Each move updates a difference-count array in O(d).
# ----------------------------------------------------------------------------

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
        # Araujo-Pardo & Lopez record family for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Main new search: Haar graphs over Z_m via difference covers of size d.
        max_m = d * (d - 1) + 1
        base_budget = max(1.0, 0.1 * time_limit)
        m_start = max(d, int(0.8 * (d * d - d + 1)))
        m = m_start
        best_m = None
        fails = 0
        while time.monotonic() < deadline and m <= max_m:
            rem = deadline - time.monotonic()
            S = _dc_anneal(d, m, rng, time.monotonic() + min(rem, base_budget))
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
                best_m = m
                fails = 0
                m += 1
            else:
                fails += 1
                if fails >= 2:
                    break
                m += 1

        # Use leftover time for a longer attempt just above the best success.
        target = (best_m + 1) if best_m is not None else m_start
        if target <= max_m and time.monotonic() < deadline:
            S = _dc_anneal(d, target, rng, deadline)
            if S is not None:
                n, e = lib.haar_graph(target, S)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
