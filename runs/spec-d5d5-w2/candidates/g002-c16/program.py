import itertools
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one attempt
ITERS = 2000                  # annealing steps per (group, connection set) try
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
WINDOW_FRAC = 0.95            # search only N in [WINDOW_FRAC * top, top] first
BUDGET_START = 0.4            # seconds per (N) attempt in the first pass
BUDGET_CAP = 3.0              # cap on per-attempt seconds as passes fail


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter. Identity is WLOG in S.
#
# The distance check is vectorised with numpy frontier sets: each BFS level is
# a handful of array operations instead of Python loops over every edge.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(N, Tn, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0.

    Tn[x, g] = x*g as an int64 array; invs[g] = inverse of g.
    A_x is adjacent to B_{Tn[x, s]} for s in S; B_y is adjacent to A_{Tn[y, s^-1]}.
    """
    Sa = np.asarray(S, dtype=np.int64)
    cf = Tn[:, Sa]              # cf[x, i]: B-neighbour index of A_x via S[i]
    cb = Tn[:, invs[Sa]]        # cb[y, i]: A-neighbour index of B_y via S[i]^-1
    total = 0
    for side in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if side == 0:
            seenA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = np.empty(0, dtype=np.int64)
        else:
            seenB[0] = True
            fB = np.array([0], dtype=np.int64)
            fA = np.empty(0, dtype=np.int64)
        for _ in range(D):
            if fA.size == 0 and fB.size == 0:
                break
            mark = np.zeros(N, dtype=bool)
            if fA.size:
                mark[cf[fA].ravel()] = True
            mark &= ~seenB
            seenB |= mark
            nB = np.flatnonzero(mark)

            mark = np.zeros(N, dtype=bool)
            if fB.size:
                mark[cb[fB].ravel()] = True
            mark &= ~seenA
            seenA |= mark
            nA = np.flatnonzero(mark)

            fA, fB = nA, nB
        total += 2 * N - int(seenA.sum()) - int(seenB.sum())
    return total


def _anneal(N, Tn, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs.

    The temperature decays geometrically from T_HOT to T_COLD, so early on the
    search can escape local minima and late on it settles greedily.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, Tn, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, Tn, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        Tn = np.array(T, dtype=np.int64)
        invs = np.array([inv(g) for g in range(N)], dtype=np.int64)
        S = _anneal(N, Tn, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2 and d >= 1:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 6)
    if top < d + 1:
        return best

    # Focus on a window near the top first: a full descending sweep wastes the
    # whole budget on orders that never succeed. The window widens downward
    # only when a whole pass finds nothing.
    floor = max(d + 1, int(WINDOW_FRAC * top))
    bestN = best_n // 2
    budget = BUDGET_START

    while time.monotonic() < deadline:
        lo = max(floor, bestN + 1)
        cands = list(range(lo, top + 1))
        if not cands:
            break
        rng.shuffle(cands)   # no fixed order: avoid a systematic bias within the window
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            bestN = max(bestN, N)
            success = True
            break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > d + 1:
                floor -= 1   # widen the window downward once budgets are maxed

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
