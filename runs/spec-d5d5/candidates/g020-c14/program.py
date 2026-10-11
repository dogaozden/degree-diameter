import itertools
import math
import random
import time

import numpy as np

import lib

ITERS = 350              # annealing steps per (group, connection set) try
GROUPS_PER_N = 8         # groups tried per order N before widening the budget
T_HOT = 1.5              # initial annealing temperature (unreached-pair units)
T_COLD = 0.1             # final annealing temperature
SCAN_WIDTH = 40          # how many consecutive orders are scanned per pass
LO_FRACTION = 0.45       # scan starts at this fraction of the Moore-type bound


# ----------------------------------------------------------------------------
# Baseline families (fast, always validated before use).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products Z_m x|_r Z_k of order N.
#
# Vertices A_x and B_y (x, y in G); edges A_x -- B_{x s} for s in S, |S| = d.
# Identity is WLOG in S. Diameter is decided by BFS from A_0 and B_0.
#
# Fast path: the full multiplication table is built with numpy, and each BFS
# level is one fancy-indexing operation instead of Python loops.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Return (M, inv): M[x, g] = index of x*g, inv[g] = index of g^{-1}; element (a, b) coded a*k+b."""
    N = m * k
    powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    a = (X // k)[:, None]
    b = (X % k)[:, None]
    c = (X // k)[None, :]
    dd = (X % k)[None, :]
    M = ((a + powers[b] * c) % m) * k + (b + dd) % k
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, inv


def _reach(M, S, Sinv, N, D, side):
    """Number of vertices within distance D of the source vertex 0 on the given side (0 = A, 1 = B)."""
    seen = (np.zeros(N, dtype=bool), np.zeros(N, dtype=bool))
    seen[side][0] = True
    front = np.zeros(1, dtype=np.int64)
    cnt = 1
    cur = side
    for _ in range(D):
        if cur == 0:
            cand = M[np.ix_(front, S)].ravel()
        else:
            cand = M[np.ix_(front, Sinv)].ravel()
        cand = np.unique(cand)
        other = seen[1 - cur]
        cand = cand[~other[cand]]
        if cand.size == 0:
            break
        other[cand] = True
        cnt += cand.size
        front = cand
        cur = 1 - cur
    return cnt


def _unreached(M, inv, S, D, N):
    """Count (source, vertex) pairs at distance > D, over sources A_0 and B_0."""
    Sa = np.asarray(S, dtype=np.int64)
    Sinv = inv[Sa]
    cnt = _reach(M, Sa, Sinv, N, D, 0) + _reach(M, Sa, Sinv, N, D, 1)
    return 4 * N - cnt


def _anneal(M, inv, N, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(M, inv, S, D, N)
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
        v = _unreached(M, inv, S2, D, N)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, d, D, rng, deadline, max_groups):
    """Try groups of order N until one yields a connection set of diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:max_groups]:
        if time.monotonic() > deadline:
            return None
        M, inv = _table(m, k, r)
        S = _anneal(M, inv, N, d, D, rng, ITERS, deadline)
        if S is not None:
            return M, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
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
        if not lib.is_valid(best[0], best[1], d, D):
            return 1, []
        return best

    # Bi-Cayley graph has 2N vertices; N is bounded by half the Moore bound.
    Nmax = lib._moore_bound(d, D) // 2
    cur_lo = max(d + 1, int(LO_FRACTION * Nmax))
    groups_budget = GROUPS_PER_N

    while time.monotonic() < deadline and cur_lo <= Nmax:
        progress = False
        hi = min(Nmax, cur_lo + SCAN_WIDTH)
        for N in range(cur_lo, hi + 1):
            if time.monotonic() >= deadline:
                break
            res = _attempt(N, d, D, rng, deadline, groups_budget)
            if res is None:
                continue
            M, S = res
            edges = [(x, N + int(M[x, g])) for x in range(N) for g in S]
            consider(2 * N, edges)
            cur_lo = N + 1
            progress = True
            break
        if not progress:
            # Nothing succeeded in this window: widen the group budget and retry.
            groups_budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
