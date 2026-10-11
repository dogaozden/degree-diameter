import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Haar graphs from difference covers (D = 3).
#
# H(m, S) has parts A = Z_m and B = Z_m with a_i ~ b_{i+s} for s in S, so it is
# d-regular and bipartite with 2m vertices. It has diameter 3 exactly when
# S - S = Z_m (a difference cover).
#
# New in this version: "targeted annealing with warm starts".
#   * Each move picks an UNCOVERED difference g and proposes y = s + g for a
#     random s in S, so the proposal directly covers g. Random proposals are
#     used only occasionally for diversity.
#   * When climbing m -> m+1, the current cover is reused as the start point
#     (reduced mod m), so the search begins close to a solution.
# ----------------------------------------------------------------------------

def _move(S, i, y, cnt, m):
    """Replace S[i] by y, updating difference counts cnt; return the change in #uncovered differences."""
    x = S[i]
    delta = 0
    for j, s in enumerate(S):
        if j == i:
            continue
        g = (x - s) % m
        cnt[g] -= 1
        if cnt[g] == 0:
            delta += 1
        g = (s - x) % m
        cnt[g] -= 1
        if cnt[g] == 0:
            delta += 1
    for j, s in enumerate(S):
        if j == i:
            continue
        g = (y - s) % m
        if cnt[g] == 0:
            delta -= 1
        cnt[g] += 1
        g = (s - y) % m
        if cnt[g] == 0:
            delta -= 1
        cnt[g] += 1
    S[i] = y
    return delta


def _cover_anneal(k, m, rng, deadline, init=None):
    """Find S subset of Z_m, |S| = k, with S - S = Z_m. Returns sorted S or None on timeout."""
    if m < k:
        return None
    if m == k:
        return list(range(m))

    # Warm start: reuse the previous cover reduced mod m, then fill with random elements.
    S, seen = [], set()
    if init:
        for x in init:
            x %= m
            if x not in seen and len(S) < k:
                S.append(x)
                seen.add(x)
    while len(S) < k:
        x = rng.randrange(m)
        if x not in seen:
            S.append(x)
            seen.add(x)
    in_s = set(S)

    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)

    T = 0.8
    it = 0
    while unc > 0:
        it += 1
        if (it & 511) == 0 and time.monotonic() > deadline:
            return None
        if it % 200000 == 0:
            T = 0.8  # reheat
        T = max(0.08, T * 0.99997)

        # Choose an uncovered difference g.
        g = rng.randrange(1, m)
        if cnt[g] != 0:
            for _ in range(30):
                g = rng.randrange(1, m)
                if cnt[g] == 0:
                    break
            else:
                g = next(gg for gg in range(1, m) if cnt[gg] == 0)

        i = rng.randrange(k)
        if rng.random() < 0.9:
            j = rng.randrange(k - 1)
            if j >= i:
                j += 1
            y = (S[j] + g) % m
        else:
            y = rng.randrange(m)
        if y in in_s:
            continue

        x = S[i]
        delta = _move(S, i, y, cnt, m)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            _move(S, i, x, cnt, m)  # revert exactly
    return sorted(S)


def _haar_search(k, rng, deadline):
    """Climb m upward with warm-started covers; return (m, S) for the largest m found, or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    m = max(k, int(0.8 * mmax))
    best = None
    prev = None
    fails = 0
    while m <= mmax and time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        slice_ = max(2.0, min(remaining / 2.0, 10.0))
        S = _cover_anneal(k, m, rng, min(deadline, now + slice_), prev)
        if S is not None:
            best = (m, S)
            prev = S
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                break
        m += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (D = 4 baseline)
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * float(time_limit), 46.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3 and d >= 2:
        res = _haar_search(d, rng, start + 0.85 * budget)
        if res is not None:
            m, S = res
            n, E = lib.haar_graph(m, S)
            consider(n, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
