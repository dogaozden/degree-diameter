import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cyclic Haar graphs from difference covers (diameter 3).
#
# H(Z_m, S) has parts a_i, b_j with a_i ~ b_{i+s} for s in S, |S| = d. It is
# d-regular and bipartite with 2m vertices. Distances from a_0:
#   - b_j is at distance 1 if j in S, and at distance 3 if j in S - S + S.
#     Since S - S = Z_m, the set S - S + S is all of Z_m, so every b_j is reached.
#   - a_i is at distance 2 iff i in S - S.
# So the graph has diameter 3 exactly when S - S = Z_m. Such S is a "difference
# cover". The Moore-type bound d(d-1)+1 >= m gives 2m <= 2(d^2-d+1), which is the
# ceiling 482 for d = 16. This is a different family from projective planes.
# ----------------------------------------------------------------------------

def _popcount(x):
    return bin(x).count("1")


def _rot(x, t, m, full):
    """Cyclic shift of an m-bit mask: bit j moves to bit (j + t) mod m."""
    t %= m
    if t == 0:
        return x
    return ((x << t) | (x >> (m - t))) & full


def _cover_bits(S, m, full):
    """Bitmask of S - S over Z_m."""
    bits = 0
    for s in S:
        bits |= 1 << s
    c = 0
    for s in S:
        c |= _rot(bits, (m - s) % m, m, full)
    return c


def _find_cover(d, m, deadline, rng):
    """Return a sorted list S of d residues mod m with S - S = Z_m, or None by the deadline."""
    if d < 1 or d > m:
        return None
    full = (1 << m) - 1
    if math.comb(m - 1, d - 1) <= 20000:
        for rest in itertools.combinations(range(1, m), d - 1):
            S = [0] + list(rest)
            if _cover_bits(S, m, full) == full:
                return S
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    cost = m - _popcount(_cover_bits(S, m, full))
    T = 1.0
    it = 0
    while cost > 0:
        if time.monotonic() > deadline:
            return None
        it += 1
        if it % 20000 == 0:
            T = 1.0
        i = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = m - _popcount(_cover_bits(S, m, full))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i] = old
        T = max(0.05, T * 0.999)
    return sorted(S)


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_end = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3 and d >= 2:
        cap = min(d * d - d + 1, 400)  # Moore-type limit on m for S - S = Z_m
        lo = max(d, int(0.75 * cap))
        ms = list(range(lo, cap + 1))
        for idx, m in enumerate(ms):
            now = time.monotonic()
            if now > budget_end:
                break
            remaining = len(ms) - idx
            dl = now + (budget_end - now) / remaining
            S = _find_cover(d, m, dl, rng)
            if S is not None:
                n_c, e_c = lib.haar_graph(m, S)
                consider(n_c, e_c)
    elif D >= 4 and time.monotonic() < budget_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
