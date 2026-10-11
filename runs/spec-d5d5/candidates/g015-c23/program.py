import itertools
import math
import random
import time

import lib

# Tunables for the cyclic bitset search.
WINDOW = 8             # candidate group orders N above the current lower bound
ATTEMPT_SECONDS = 6.0  # wall-clock budget per (N, restart) attempt
TEMP0 = 2.0            # initial annealing temperature
TEMP_MIN = 0.3         # temperature floor
COOL = 0.9995          # per-step multiplicative cooling


# ----------------------------------------------------------------------------
# Structured baselines for D = 3 and D = 4.
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
# NEW HELPER: bitset-rotation evaluator for cyclic bi-Cayley lifts.
#
# The lift over Z_N with connection set S has A_x ~ B_{x+g} for g in S.
# Represent a set of A-indices (or B-indices) as an N-bit integer. Then
#   {x + g : x in R}  is  OR over g of rot(R, g),
# and a whole BFS layer costs d big-int rotations instead of N*d list steps.
# Translation symmetry means only sources A_0 and B_0 need checking.
# ----------------------------------------------------------------------------

def _rot(mask, s, N, full):
    """Cyclically rotate an N-bit mask so that bit x moves to bit (x + s) mod N."""
    s %= N
    if s == 0:
        return mask
    return ((mask << s) | (mask >> (N - s))) & full


def _sumset(mask, shifts, N, full):
    """Minkowski sum {x + s : x in mask, s in shifts} as an N-bit mask."""
    out = 0
    for g in shifts:
        out |= _rot(mask, g, N, full)
    return out


def _cyc_cost(N, S, D, full):
    """Number of (source, vertex) pairs at distance > D, for sources A_0 and B_0. Zero means valid."""
    Sneg = [(-g) % N for g in S]
    total = 0
    for a_side in (True, False):
        Ra = 1 if a_side else 0   # cumulative A-vertices within current radius
        Rb = 0 if a_side else 1   # cumulative B-vertices within current radius
        for _ in range(D):
            nb = Rb | _sumset(Ra, S, N, full)
            na = Ra | _sumset(Rb, Sneg, N, full)
            Ra, Rb = na, nb
        total += 2 * N - Ra.bit_count() - Rb.bit_count()
    return total


def _cyc_search(N, d, D, rng, deadline):
    """Anneal a d-element set S in Z_N (0 fixed WLOG) until the lift Haar(N, S) has diameter <= D."""
    if N < d + 1:
        return None
    full = (1 << N) - 1
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cyc_cost(N, S, D, full)
    T = TEMP0
    it = 0
    while cur > 0:
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        it += 1
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _cyc_cost(N, S, D, full)
        if v <= cur or rng.random() < math.exp(-(v - cur) / T):
            cur = v
        else:
            S[i] = old
        T = max(TEMP_MIN, T * COOL)
    return list(S) if cur == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d} meets the Moore bound 2d
    if d == 2:
        n = 2 * D                                   # even cycle C_{2D}: degree 2, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Cyclic bi-Cayley search: a lift on Z_N has 2N vertices.
    # Aim just above the current record, so every success raises the bar.
    while best[0] < moore and time.monotonic() < deadline:
        base = best[0] // 2 + 1
        if base > moore // 2:
            break
        N = base + rng.randrange(WINDOW)
        if N > moore // 2:
            N = base
        att = min(deadline, time.monotonic() + ATTEMPT_SECONDS)
        S = _cyc_search(N, d, D, rng, att)
        if S is not None:
            consider(*lib.haar_graph(N, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
