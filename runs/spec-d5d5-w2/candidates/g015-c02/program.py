import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines for D = 3 and D = 4 (kept from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction for D >= 3: voltage lifts over Z_N with k base vertices per
# side (2kN vertices, degree d). Distances are computed with big-integer
# bitsets: a rotation of an N-bit mask is one shift-or, so one evaluation of
# the "unreached pairs" cost is a few hundred word operations.
#
# Vertex A_{i,x} (block i, x in Z_N) is joined to B_{j,x+s} for each dart (i,j,s).
# Translation by Z_N is an automorphism, so checking BFS from A_{i,0} and B_{j,0}
# for every block i, j certifies the whole diameter.
# ----------------------------------------------------------------------------

def _rot(X, s, N, full):
    """Rotate the N-bit set X by s on Z_N (bit x moves to bit x+s mod N)."""
    if s == 0:
        return X
    return ((X << s) | (X >> (N - s))) & full


def _reach(k, N, D, Aout, Bin, full, side, a):
    """Number of vertices within distance D of source (side, block a, element 0)."""
    RA = [0] * k
    RB = [0] * k
    FA = [0] * k
    FB = [0] * k
    if side == 0:
        FA[a] = 1
        RA[a] = 1
    else:
        FB[a] = 1
        RB[a] = 1
    reached = 1
    cur = side
    for _ in range(D):
        if cur == 0:
            NB = [0] * k
            for i in range(k):
                x = FA[i]
                if x:
                    for j, s in Aout[i]:
                        NB[j] |= _rot(x, s, N, full)
            nf = [0] * k
            any_new = False
            for j in range(k):
                f = NB[j] & ~RB[j]
                if f:
                    RB[j] |= f
                    reached += f.bit_count()
                    nf[j] = f
                    any_new = True
            if not any_new:
                break
            FB = nf
            FA = [0] * k
            cur = 1
        else:
            NA = [0] * k
            for j in range(k):
                x = FB[j]
                if x:
                    for i, t in Bin[j]:
                        NA[i] |= _rot(x, t, N, full)
            nf = [0] * k
            any_new = False
            for i in range(k):
                f = NA[i] & ~RA[i]
                if f:
                    RA[i] |= f
                    reached += f.bit_count()
                    nf[i] = f
                    any_new = True
            if not any_new:
                break
            FA = nf
            FB = [0] * k
            cur = 0
    return reached


def _cost(k, N, D, darts, full):
    """Unreached (source, vertex) pairs over all 2k block sources, plus a duplicate penalty."""
    Aout = [[] for _ in range(k)]
    Bin = [[] for _ in range(k)]
    for i, j, s in darts:
        Aout[i].append((j, s))
        Bin[j].append((i, (N - s) % N))
    V = 2 * k * N
    dup = len(darts) - len(set(darts))
    total = dup * V
    for side in (0, 1):
        for a in range(k):
            total += V - _reach(k, N, D, Aout, Bin, full, side, a)
    return total


def _anneal(k, N, d, D, rng, end):
    """Time-scheduled simulated annealing for darts (i, j, s); returns darts with zero cost or None."""
    E = k * d
    full = (1 << N) - 1
    js = [t % k for t in range(E)]
    rng.shuffle(js)  # each B_j receives exactly d darts
    darts = [(t // d, js[t], rng.randrange(N)) for t in range(E)]
    cost = _cost(k, N, D, darts, full)
    if cost == 0:
        return darts
    T0 = min(40.0, max(2.0, 0.05 * cost))
    T1 = 0.2
    t_start = time.monotonic()
    span = max(1e-3, end - t_start)
    while True:
        now = time.monotonic()
        if now >= end:
            break
        frac = (now - t_start) / span
        T = T0 * (T1 / T0) ** frac
        if rng.random() < 0.6:
            t = rng.randrange(E)
            s_new = rng.randrange(N)
            i, j, s = darts[t]
            if s_new == s:
                continue
            new = list(darts)
            new[t] = (i, j, s_new)
        else:
            t1 = rng.randrange(E)
            t2 = rng.randrange(E)
            a = darts[t1]
            b = darts[t2]
            if a[1] == b[1]:
                continue
            new = list(darts)
            new[t1] = (a[0], b[1], a[2])
            new[t2] = (b[0], a[1], b[2])
        c2 = _cost(k, N, D, new, full)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            darts = new
            cost = c2
            if cost == 0:
                return darts
    return None


def _edges(k, N, darts):
    """Expand darts into the (n, edges) lift."""
    E = set()
    for i, j, s in darts:
        for x in range(N):
            E.add((i * N + x, (k + j) * N + (x + s) % N))
    return 2 * k * N, sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every d >= 1.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: ratchet the order upward with bitset-evaluated voltage lifts.
    if best[0] < moore:
        try:
            slice_len = max(2.0, budget / 6.0)
            while time.monotonic() < deadline and best[0] < moore:
                now = time.monotonic()
                best_n = best[0]
                k = rng.choice((1, 2, 2, 3, 3, 4))
                lo = best_n // (2 * k) + 1
                hi = min(moore // (2 * k), lo + max(4, lo // 6))
                if hi < lo:
                    continue
                N = lo + min(hi - lo, int((rng.random() ** 2) * (hi - lo + 1)))
                if N < d:
                    N = d
                if N > hi:
                    continue
                slice_end = min(deadline, now + slice_len)
                darts = _anneal(k, N, d, D, rng, slice_end)
                if darts is not None:
                    n2, e2 = _edges(k, N, darts)
                    consider(n2, e2)
        except Exception:
            pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
