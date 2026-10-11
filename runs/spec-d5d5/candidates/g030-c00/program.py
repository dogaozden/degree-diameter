import itertools
import math
import random
import time

import numpy as np

import lib

ITERS = 40000                 # annealing steps per (group, connection set) try
MAX_GROUPS_PER_ATTEMPT = 16   # groups tried per order N within one attempt
T_HOT = 1.2                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.08                 # final annealing temperature


# ----------------------------------------------------------------------------
# Baseline families (used for D = 3 and D = 4 calibration-style cases).
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
# Bi-Cayley search over groups of order N.
#
# Vertices A_x, B_y (x, y in G); edge A_x -- B_{x s} for s in S, |S| = d, 1 in S.
# New helper: the reachability check is a vectorized frontier propagation in
# numpy (fancy indexing on a precomputed multiplication table), replacing a
# Python BFS. This gives roughly an order of magnitude more annealing steps
# per second, so the search can afford far longer runs for the target cases.
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


def _unreached_np(N, Tarr, S, Sinv, D):
    """Total unreached (source, vertex) pairs for sources A_0 and B_0, via numpy frontiers."""
    total = 0
    for side in (0, 1):
        fa = np.zeros(N, dtype=bool)
        fb = np.zeros(N, dtype=bool)
        if side == 0:
            fa[0] = True
        else:
            fb[0] = True
        ra = fa.copy()
        rb = fb.copy()
        for _ in range(D):
            nb = np.zeros(N, dtype=bool)
            if fa.any():
                nb[Tarr[fa][:, S].ravel()] = True
            na = np.zeros(N, dtype=bool)
            if fb.any():
                na[Tarr[fb][:, Sinv].ravel()] = True
            nb &= ~rb
            na &= ~ra
            rb |= nb
            ra |= na
            fa, fb = na, nb
            if not (fa.any() or fb.any()):
                break
        total += 2 * N - int(ra.sum()) - int(rb.sum())
    return total


def _anneal(N, Tarr, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = np.array([0] + rng.sample(range(1, N), d - 1), dtype=np.int64)

    def ev(Sv):
        return _unreached_np(N, Tarr, Sv, invs[Sv], D)

    cur = ev(S)
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S.copy()
        S2[i] = c
        v = ev(S2)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set of diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        Tarr = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
        invs = np.array([inv(g) for g in range(N)], dtype=np.int64)
        S = _anneal(N, Tarr, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return Tarr, S
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

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 14)
    cands = set(range(d + 1, top + 1))

    budget = 0.5
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
            Tarr, S = res
            edges = [(x, N + int(Tarr[x, g])) for x in range(N) for g in S]
            consider(2 * N, edges)
            # Only larger orders can improve now; allow one step above the success.
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
