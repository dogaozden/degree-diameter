import itertools
import math
import random
import time

import lib

MAX_GROUPS = 25        # groups tried per (k, N) attempt
ITERS = 700            # annealing steps per attempt
ATTEMPT_BUDGET = 3.0   # seconds per (k, N) attempt


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
# Multi-orbit voltage lifts over semidirect products.
#
# Group G of order N acts by left multiplication. A side has k orbits:
# A_i,x for i < k and B_j,y for j < k, with x, y in G.
# Block (i, j) carries a connection set S_ij in G, and the edges are
# A_i,x -- B_j,x*s for s in S_ij. Left multiplication is an automorphism,
# so distances from the k+k orbit identities cover every vertex pair.
#
# New helper here: the degree split C (a k x k matrix whose rows and columns
# sum to d). For k = 2, C = [[a, d-a], [d-a, a]] lets one search mix several
# orbits. The lift has 2kN vertices, so k = 2 gives 4N vertices.
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


def _blocks(k, d, rng):
    """Random degree-split matrix with all row and column sums equal to d."""
    if k == 1:
        return [[d]]
    a = rng.randint(1, d - 1)
    return [[a, d - a], [d - a, a]]


def _unreached(k, N, T, S, D):
    """Count (source, vertex) pairs not within distance D, over the 2k orbit identities."""
    V = 2 * k * N
    adj = [[] for _ in range(V)]
    for (i, j), lst in S.items():
        bj = (k + j) * N
        for s in lst:
            for x in range(N):
                a = i * N + x
                b = bj + T[x][s]
                adj[a].append(b)
                adj[b].append(a)
    total = 0
    for src in range(0, V, N):
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _anneal(k, N, T, C, D, rng, iters, deadline):
    """Anneal the connection sets, one per nonzero block, to zero unreached pairs."""
    blocks = [(i, j) for i in range(k) for j in range(k) if C[i][j] > 0]
    S = {b: rng.sample(range(N), C[b[0]][b[1]]) for b in blocks}
    cur = _unreached(k, N, T, S, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 1.5 * (1.0 - it / iters))
        b = rng.choice(blocks)
        lst = S[b]
        t = rng.randrange(len(lst))
        c = rng.randrange(N)
        if c in lst:
            continue
        new = lst[:]
        new[t] = c
        S2 = dict(S)
        S2[b] = new
        v = _unreached(k, N, T, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N with random degree splits until one lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        C = _blocks(k, d, rng)
        S = _anneal(k, N, T, C, D, rng, ITERS, deadline)
        if S is not None:
            return C, S, T
    return None


def _edges(k, N, T, S):
    """Expand a lift into (n, edges). A orbits come first, then B orbits."""
    e = []
    for (i, j), lst in S.items():
        bj = (k + j) * N
        for s in lst:
            for x in range(N):
                e.append((i * N + x, bj + T[x][s]))
    return 2 * k * N, e


def _search(k, Ns, d, D, rng, end, consider, frac):
    """Search candidate orders; after each hit, only larger orders remain.

    frac < 1 restricts each pick to the lowest fraction of remaining candidates.
    """
    cands = sorted(Ns)
    while cands and time.monotonic() < end:
        pool = cands[: max(1, int(len(cands) * frac))]
        N = rng.choice(pool)
        now = time.monotonic()
        res = _attempt(k, N, d, D, rng, min(end, now + ATTEMPT_BUDGET))
        if res is None:
            continue
        C, S, T = res
        n, e = _edges(k, N, T, S)
        consider(n, e)
        cands = [M for M in cands if M > N]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

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

    if d < 2 or D < 2 or time.monotonic() >= deadline:
        return best[0], best[1]

    moore = lib._moore_bound(d, D)

    # Phase A: plain bi-Cayley (k = 1) near the Moore-half scale.
    now = time.monotonic()
    phase_a_end = now + 0.3 * (deadline - now)
    lo1 = max(2, moore // 4 - 12)
    hi1 = moore // 4 + 8
    _search(1, range(lo1, hi1 + 1), d, D, rng, phase_a_end, consider, 1.0)

    # Phase B: two orbits per side, order 4N, only orders that beat the current best.
    lo2 = best[0] // 4 + 1
    hi2 = moore // 4
    if lo2 <= hi2 and time.monotonic() < deadline:
        _search(2, range(lo2, hi2 + 1), d, D, rng, deadline, consider, 0.34)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
