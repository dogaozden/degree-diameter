import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Difference-covering Haar graphs (diameter 3, bipartite, degree k).
#
# H(m, S) has A_i joined to B_{i+s} for s in S. Two A-vertices are at distance
# <= 2 exactly when their index difference lies in S - S, so if S - S covers
# all of Z_m then every A-A pair is within 2, and every A-B pair is within 3
# (since (S - S) + S = Z_m). Diameter 3 then holds. The Moore-type limit is
# |S|(|S| - 1) + 1 >= m.
# ----------------------------------------------------------------------------

def _replace(S, cnt, m, i, x):
    """Replace S[i] by x, updating the ordered-difference counts cnt.

    Returns the change in the number of uncovered nonzero residues.
    """
    k = len(S)
    old = S[i]
    delta = 0
    for j in range(k):
        if j == i:
            continue
        y = S[j]
        r = (old - y) % m
        cnt[r] -= 1
        if cnt[r] == 0:
            delta += 1
        r = (y - old) % m
        cnt[r] -= 1
        if cnt[r] == 0:
            delta += 1
    S[i] = x
    for j in range(k):
        if j == i:
            continue
        y = S[j]
        r = (x - y) % m
        if cnt[r] == 0:
            delta -= 1
        cnt[r] += 1
        r = (y - x) % m
        if cnt[r] == 0:
            delta -= 1
        cnt[r] += 1
    return delta


def _cover_search(m, k, rng, deadline):
    """Annealing search for a k-subset S of Z_m with S - S = Z_m. Returns S or None."""
    if k < 1 or k > m or k * (k - 1) + 1 < m:
        return None
    S = rng.sample(range(m), k)
    inS = [False] * m
    for x in S:
        inS[x] = True
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 0.6
    it = 0
    while unc > 0:
        it += 1
        if (it & 511) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = (now - t0) / span
            T = 0.6 * (0.03 ** frac)
        i = rng.randrange(k)
        x = None
        if rng.random() < 0.7:
            # Focused move: create a currently uncovered difference r.
            r = None
            for _ in range(40):
                c = rng.randrange(1, m)
                if cnt[c] == 0:
                    r = c
                    break
            if r is not None:
                j = rng.randrange(k)
                if j == i:
                    continue
                if rng.random() < 0.5:
                    x = (S[j] + r) % m
                else:
                    x = (S[j] - r) % m
        if x is None:
            x = rng.randrange(m)
        if inS[x]:
            continue
        old = S[i]
        delta = _replace(S, cnt, m, i, x)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            inS[old] = False
            inS[x] = True
            unc += delta
        else:
            _replace(S, cnt, m, i, old)
    return S


# ----------------------------------------------------------------------------
# Projective plane fallback (diameter 3).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 40), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane incidence graph (diameter 3, degree q + 1 <= d).
    pg = _pg_candidate(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Main family: Haar graphs whose connection set S (|S| = d) has S - S = Z_m.
    # Climb m upward while the annealing search keeps succeeding.
    mmax = d * (d - 1) + 1
    m = min(mmax, max(d + 1, (d * d) // 2))
    tries = 0
    slice_len = max(2.0, 0.2 * budget)
    while m <= mmax:
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = min(deadline, now + slice_len)
        S = _cover_search(m, d, rng, slice_end)
        if S is None:
            tries += 1
            if tries >= 3:
                break
            continue
        tries = 0
        n2, e2 = lib.haar_graph(m, S)
        consider(n2, e2)
        m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
