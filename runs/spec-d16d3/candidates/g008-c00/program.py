import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Difference-basis Haar graphs.
#
# Bipartite Haar graph H(m, S): A_i ~ B_j iff j - i in S, |S| = d.
# If S - S covers all of Z_m, then diameter <= 3:
#   same-side pairs have distance <= 2 (their difference lies in S - S),
#   cross pairs have distance <= 3 (their difference lies in (S - S) + S = Z_m).
# So the task reduces to finding a k-subset of Z_m whose difference set covers Z_m.
# Order 2m, degree k. Simulated annealing over S with incremental coverage counts.
# ----------------------------------------------------------------------------

def _shift(cnt, m, x, others, sign):
    """Add (sign > 0) or remove (sign < 0) the ordered differences between x and each element of others.

    Returns the change in the number of uncovered residues 1..m-1.
    """
    change = 0
    if sign < 0:
        for s in others:
            for r in ((x - s) % m, (s - x) % m):
                cnt[r] -= 1
                if cnt[r] == 0:
                    change += 1
    else:
        for s in others:
            for r in ((x - s) % m, (s - x) % m):
                if cnt[r] == 0:
                    change -= 1
                cnt[r] += 1
    return change


def _search_difference_basis(m, k, rng, deadline):
    """Anneal a k-subset S of Z_m (0 in S) with S - S = Z_m. Returns S or None."""
    if m < k or m < 2 or k < 2:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    uncovered = sum(1 for r in range(1, m) if cnt[r] == 0)
    inS = [False] * m
    for a in S:
        inS[a] = True

    it = 0
    while uncovered > 0:
        if it & 1023 == 0 and time.monotonic() > deadline:
            break
        it += 1
        phase = it % 20000
        T = max(0.15, 0.9997 ** phase)

        i = rng.randrange(1, k)
        y = rng.randrange(1, m)
        if inS[y]:
            continue
        x = S[i]
        others = S[:i] + S[i + 1:]

        delta = _shift(cnt, m, x, others, -1)
        delta += _shift(cnt, m, y, others, 1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            uncovered += delta
            S[i] = y
            inS[x] = False
            inS[y] = True
        else:
            _shift(cnt, m, y, others, -1)
            _shift(cnt, m, x, others, 1)

    return S if uncovered == 0 else None


# ----------------------------------------------------------------------------
# Projective-plane baseline (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.78 * time_limit
    rng = random.Random(seed * 1000003 + d * 31 + D)

    if D < 1 or d < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # D >= 3: projective-plane baseline first (cheap, valid).
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Main family: difference-basis Haar graphs with |S| = d.
    k = d
    m_hi = k * k - k + 1  # hard upper bound on m for |S - S| coverage
    per_attempt = max(0.5, 0.06 * time_limit)
    best_m = 0
    m = max(k, int(0.85 * m_hi))

    while time.monotonic() < deadline:
        if best_m >= m:
            m = best_m + 1
        if m > m_hi:
            break
        attempt_deadline = min(deadline, time.monotonic() + per_attempt)
        S = _search_difference_basis(m, k, rng, attempt_deadline)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            if lib.is_valid(n, e, d, D):
                best_m = m
                consider(n, e)
            m += 1
        else:
            m = max(k, best_m + 1, m - 1)

    n, e = best
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return best
