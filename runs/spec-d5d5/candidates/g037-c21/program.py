import itertools
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 40  # groups tried per order N within one attempt
STEPS = 150                  # local-search steps per (group) try
NOISE = 0.12                 # probability of a random (not greedy) slot replacement
TOP_FRAC = 0.6               # search orders up to TOP_FRAC * Nmax + TOP_SLACK
TOP_SLACK = 8


# ----------------------------------------------------------------------------
# Baseline families (fast, always validated with lib.is_valid before use).
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
# Bi-Cayley graphs over semidirect products Z_m x|_r Z_k of order N.
#
# Vertices A_x, B_y (x, y in G). Edge A_x -- B_{x s} for s in S (|S| = d, 0 in S).
# Left multiplication is an automorphism, so diameter <= D iff every pair
# (A_0, *) and (B_0, *) is within distance D.
#
# NEW: exact batched evaluation. For a fixed set of d-1 generators plus a whole
# vector of candidate values for the last generator, we compute the number of
# unreached pairs for ALL candidates at once with numpy boolean reach-set
# propagation. A local-search step then performs a full "best replacement"
# move over every candidate in one vectorized call, instead of one BFS per
# candidate.
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


def _tables(N, m, k, r):
    """Multiplication table T[x, g] = x*g and TI[y, s] = y * s^{-1} for Z_m x|_r Z_k (element a*k+b)."""
    powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    ax, bx = (X // k)[:, None], (X % k)[:, None]
    cg, dg = (X // k)[None, :], (X % k)[None, :]
    T = ((ax + powers[bx] * cg) % m) * k + (bx + dg) % k
    invs = np.argmax(T == 0, axis=1)  # invs[x] = inverse of x (T[x, inv] = identity 0)
    TI = T[:, invs]                   # TI[y, s] = y * s^{-1}
    return T, TI


def _cost(T, TI, fixed, cand, N, D):
    """Unreached-pair count for the generator set fixed + [c] for every c in cand (vectorized).

    Sources are A_0 and B_0. Reach sets grow by R_t = R_{t-1} | N(R_{t-1}).
    """
    C = len(cand)
    rows = np.arange(C)[:, None]
    ga = [T[:, s][None, :] for s in fixed]
    gb = [TI[:, s][None, :] for s in fixed]
    ga.append(T[:, cand].T)     # ga[j][c, x] = x * cand_c       (A -> B step)
    gb.append(TI[:, cand].T)    # gb[j][c, y] = y * cand_c^{-1}  (B -> A step)
    total = np.zeros(C, dtype=np.int64)
    for side in (0, 1):
        Ra = np.zeros((C, N), dtype=bool)
        Rb = np.zeros((C, N), dtype=bool)
        if side == 0:
            Ra[:, 0] = True
        else:
            Rb[:, 0] = True
        for _ in range(D):
            na = np.zeros((C, N), dtype=bool)
            nb = np.zeros((C, N), dtype=bool)
            for ia in ga:
                na |= Rb[rows, ia]
            for ib in gb:
                nb |= Ra[rows, ib]
            Ra |= na
            Rb |= nb
        total += 2 * N - Ra.sum(axis=1) - Rb.sum(axis=1)
    return total


def _search(N, T, TI, d, D, rng, deadline, steps):
    """Local search over S = {0, s_1, ..., s_{d-1}}: each step rewrites one slot to its best value."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = int(_cost(T, TI, S[:-1], np.array([S[-1]], dtype=np.int64), N, D)[0])
    for _ in range(steps):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(1, d)
        fixed = [S[j] for j in range(d) if j != i]
        fs = set(fixed)
        cand = np.array([c for c in range(1, N) if c not in fs], dtype=np.int64)
        costs = _cost(T, TI, fixed, cand, N, D)
        if rng.random() < NOISE:
            j = rng.randrange(len(cand))
        else:
            mn = int(costs.min())
            opts = np.flatnonzero(costs == mn)
            j = int(opts[rng.randrange(len(opts))])
        S[i] = int(cand[j])
        cur = int(costs[j])
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        T, TI = _tables(N, m, k, r)
        S = _search(N, T, TI, d, D, rng, deadline, STEPS)
        if S is not None:
            return T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D >= 2:
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

    Nmax = lib._moore_bound(d, D) // 2  # bi-Cayley graph has 2N vertices
    top = min(Nmax, int(Nmax * TOP_FRAC) + TOP_SLACK)
    cands = set(range(d + 1, top + 1))

    budget = 0.4
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            edges = [(x, N + int(T[x, g])) for x in range(N) for g in S]
            consider(2 * N, edges)
            # Only larger orders can improve now; allow one step above the success.
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
