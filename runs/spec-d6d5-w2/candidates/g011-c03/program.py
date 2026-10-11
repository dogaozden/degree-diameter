import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic families for small D: projective plane, Araujo-Pardo-Lopez graph,
# and the generalized quadrangle W(q) for D >= 4.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


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
# New family for D >= 5: Haar graphs H(Z_m, S) with |S| = d, searched with
# bit-parallel reachability.
#
# Vertices a_i (i in Z_m) and b_j; a_i ~ b_{i+s} for s in S.
# Translations act transitively on each side, so the diameter is <= D iff
# every vertex is within distance D of a_0 AND of b_0. This makes one
# evaluation cost only O(D * d) big-integer rotations.
# ----------------------------------------------------------------------------

def _rot(x, s, m, full):
    """Cyclically rotate an m-bit mask so that bit i moves to bit (i + s) mod m."""
    s %= m
    if s == 0:
        return x
    return ((x << s) | (x >> (m - s))) & full


def _haar_unreached(m, S, D, full):
    """Number of (source, vertex) pairs at distance > D, sources a_0 and b_0. Zero means diameter <= D."""
    neg = [(m - s) % m for s in S]
    total = 0
    for side in (0, 1):
        A = 1 if side == 0 else 0   # ball of radius t around the source, A side
        B = 0 if side == 0 else 1   # B side
        for _ in range(D):
            nB = B
            for s in S:
                nB |= _rot(A, s, m, full)
            nA = A
            for t in neg:
                nA |= _rot(B, t, m, full)
            A, B = nA, nB
        total += (m - A.bit_count()) + (m - B.bit_count())
    return total


def _search_haar(m, d, D, rng, deadline, iters):
    """Annealed search for S (|S| = d, 0 in S) so that H(Z_m, S) has diameter <= D. Returns S or None."""
    if m < d:
        return None
    full = (1 << m) - 1
    others = list(range(1, m))
    S = [0] + rng.sample(others, d - 1)
    c = _haar_unreached(m, S, D, full)
    T = 2.0
    for it in range(iters):
        if c == 0:
            return S
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        cand = rng.randrange(1, m)
        if cand in S:
            continue
        Tn = S[:]
        Tn[i] = cand
        ct = _haar_unreached(m, Tn, D, full)
        if ct <= c or rng.random() < math.exp(-(ct - c) / T):
            S, c = Tn, ct
        T = max(0.3, T * 0.999)
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search for D >= 5: Haar graphs over cyclic groups, with m sampled
    # just above the current best order / 2.
    if D >= 5 and d >= 2:
        lo = best_n // 2 + 1
        while time.monotonic() < deadline:
            m = lo + rng.randrange(0, 40)
            S = _search_haar(m, d, D, rng, deadline, 2500)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
                lo = max(lo, best_n // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
