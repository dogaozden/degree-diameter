import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per attempt
ITERS = 600                   # annealing steps per attempt
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
ATTEMPT_SEC = 1.5             # seconds per sampled (k, N) attempt
FAIL_STEP = 6                 # consecutive failures before the window drops
P_K2 = 0.7                    # probability of trying the two-orbit (k=2) family


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
# Multi-orbit bi-Cayley search (NEW in this version).
#
# Base graph has k vertices on each side: A_0..A_{k-1}, B_0..B_{k-1}. Each group
# element gives one copy of the base graph; the lift has 2*k*N vertices.
# Block (i, j) carries a connection set S[i][j] subset of G, and
#   A_i,x is adjacent to B_j,(x*s) for every s in S[i][j].
# Left multiplication is an automorphism, so eccentricities from A_i,1 and B_j,1
# (2k sources) decide the diameter. Choosing block sizes
#   [[a, d-a], [d-a, a]]
# makes every vertex have degree exactly d. With k = 1 this is the usual
# bi-Cayley graph, so the old family is recovered as a special case.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


def _unreached(N, k, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, over the 2k class sources."""
    V = 2 * k * N
    offB = k * N
    Sinv = [[[invs[s] for s in S[i][j]] for j in range(k)] for i in range(k)]
    sources = [i * N for i in range(k)] + [offB + j * N for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < offB:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j in range(k):
                        base = offB + j * N
                        for s in S[i][j]:
                            v = base + row[s]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    j, y = divmod(u - offB, N)
                    row = T[y]
                    for i in range(k):
                        ib = i * N
                        for h in Sinv[i][j]:
                            v = ib + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, k, T, invs, sizes, D, rng, iters, deadline):
    """Simulated annealing over the k*k connection sets to zero unreached pairs."""
    S = [[rng.sample(range(N), sizes[i][j]) for j in range(k)] for i in range(k)]
    cur = _unreached(N, k, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(k)
        j = rng.randrange(k)
        idx = rng.randrange(sizes[i][j])
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        S2 = [[list(S[a][b]) for b in range(k)] for a in range(k)]
        S2[i][j][idx] = c
        v = _unreached(N, k, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, k, d, D, rng, deadline):
    """Try groups of order N for base size k until one yields diameter <= D, or time runs out."""
    if k == 1:
        sizes = [[d]]
    else:
        a = rng.randint(1, d - 1)
        sizes = [[a, d - a], [d - a, a]]
    groups = _groups(N)
    rng.shuffle(groups)
    for gm, gk, gr in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(gm, gk, gr)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, k, T, invs, sizes, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _lift_edges(N, k, T, S):
    """Edges of the k-base bi-Cayley lift: A_i,x -- B_j,(x*s) for s in S[i][j]."""
    offB = k * N
    edges = []
    for i in range(k):
        for j in range(k):
            base = offB + j * N
            for x in range(N):
                row = T[x]
                for s in S[i][j]:
                    edges.append((i * N + x, base + row[s]))
    return edges


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

    moore = lib._moore_bound(d, D)
    # Windows of base size k: total order is 2*k*N, so N ranges over [lo, top].
    tops = {}
    lo = {}
    nmax1 = moore // 2
    tops[1] = min(nmax1, nmax1 // 2 + 6)
    lo[1] = max(d + 1, int(0.9 * tops[1]))
    tops[2] = moore // 4
    lo[2] = max(d + 1, tops[2] // 2)
    fails = {1: 0, 2: 0}
    valid_k = [k for k in (1, 2) if tops[k] >= d + 1 and tops[k] >= lo[k]]
    if not valid_k:
        return best

    while time.monotonic() < deadline:
        if len(valid_k) == 2:
            k = 2 if rng.random() < P_K2 else 1
        else:
            k = valid_k[0]
        top = tops[k]
        cur_lo = min(max(lo[k], d + 1), top)
        N = rng.randint(cur_lo, top)
        now = time.monotonic()
        if now >= deadline:
            break
        att_deadline = min(deadline, now + ATTEMPT_SEC)
        res = _attempt(N, k, d, D, rng, att_deadline)
        if res is None:
            fails[k] += 1
            if fails[k] >= FAIL_STEP:
                fails[k] = 0
                lo[k] = max(d + 1, lo[k] - 2)
            continue
        T, S = res
        consider(2 * k * N, _lift_edges(N, k, T, S))
        lo[k] = N + 1
        fails[k] = 0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
