import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D = 3: cyclic Haar graphs from difference covers.
#
# H(m, S) has points i and lines m+j, with i ~ m+j iff j - i (mod m) lies in S.
# If |S| = d, it is d-regular and bipartite with 2m vertices. Its diameter is
# at most 3 exactly when S - S covers all of Z_m. Point-point and line-line
# pairs need a difference in S - S. Point-line pairs need x in S - S + S, which
# follows from S - S = Z_m. So the task is to find a d-subset of Z_m whose
# differences cover Z_m, with m as large as possible (m <= d(d-1)+1).
# ----------------------------------------------------------------------------

def _bump(cnt, r, dlt):
    """Update cnt[r] by dlt; return the change in the number of uncovered residues."""
    old = cnt[r]
    new = old + dlt
    cnt[r] = new
    if old == 0 and new > 0:
        return -1
    if old > 0 and new == 0:
        return 1
    return 0


def _swap(S, cnt, m, i, x):
    """Replace S[i] by x, updating difference counts. Return the change in uncovered residues."""
    s = S[i]
    du = 0
    for j, t in enumerate(S):
        if j == i:
            continue
        du += _bump(cnt, (s - t) % m, -1)
        du += _bump(cnt, (t - s) % m, -1)
    for j, t in enumerate(S):
        if j == i:
            continue
        du += _bump(cnt, (x - t) % m, 1)
        du += _bump(cnt, (t - x) % m, 1)
    S[i] = x
    return du


def _cover_search(m, k, rng, deadline, iters):
    """Simulated annealing for a k-subset of Z_m whose difference set is all of Z_m. Returns list or None."""
    S = rng.sample(range(m), k)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)
    if unc == 0:
        return S
    inS = set(S)
    for it in range(iters):
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        T = 1.0 * (0.08 ** (it / iters))
        i = rng.randrange(k)
        x = rng.randrange(m)
        if x in inS:
            continue
        old = S[i]
        du = _swap(S, cnt, m, i, x)
        if du <= 0 or rng.random() < math.exp(-du / T):
            inS.discard(old)
            inS.add(x)
            unc += du
            if unc == 0:
                return S
        else:
            _swap(S, cnt, m, i, old)  # exact inverse
    return None


def _cyclic_cover_search(d, deadline, rng):
    """Find the largest m (ascending from d) with a d-element difference cover of Z_m. Return (m, S) or None."""
    best = None
    m = d
    mmax = d * (d - 1) + 1
    while m <= mmax and time.monotonic() < deadline:
        S = None
        while S is None and time.monotonic() < deadline:
            S = _cover_search(m, d, rng, deadline, iters=80000)
        if S is None:
            break
        best = (m, sorted(S))
        m += 1
    return best


# ----------------------------------------------------------------------------
# Fallback for D >= 4 (not a scored target here): random Haar graphs checked
# directly for diameter.
# ----------------------------------------------------------------------------

def _haar_random(d, D, rng, deadline):
    best = lib.haar_graph(d, range(d))
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe baseline: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)]) if d >= 1 and lib.is_valid(2, [(0, 1)], d, D) else (1, [])

    if D == 2:
        return best

    if D == 3:
        # Structured candidates from the previous approach (kept as safe alternatives).
        cands = []
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            try:
                cands.append(lib.projective_plane_incidence(d - 1))
            except Exception:
                pass
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        for n, e in cands:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)

        # Main search: cyclic Haar graph from a difference cover.
        res = _cyclic_cover_search(d, deadline, rng)
        if res is not None:
            m, S = res
            n, e = lib.haar_graph(m, S)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        return best

    # Other diameters: random Haar search with direct diameter checks.
    cand = _haar_random(d, D, rng, deadline)
    if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
        best = cand
    return best
