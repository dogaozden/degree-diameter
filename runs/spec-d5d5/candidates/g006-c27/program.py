import itertools
import math
import random
import time

import lib

ITERS = 500          # annealing steps per (group, base permutations) try
MAX_GROUPS = 25      # groups tried per (base size, order N) attempt
KS = (1, 2, 3, 4)    # base graphs with b vertices per side (b = 1 is the bi-Cayley case)
MAX_BUDGET = 15.0    # cap on per-attempt time in seconds


# ----------------------------------------------------------------------------
# Baseline families (fast, valid when they pass lib.is_valid).
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
# New helper: multi-orbit voltage lifts over a d-regular bipartite base.
#
# Base graph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}. It is built
# from d perfect matchings sigma_0..sigma_{d-1} (permutations of range(b)), so
# each base vertex has exactly degree d. Dart i,j joins A_j to B_{sigma_i(j)}
# with a voltage g in a group G of order N. The lift has 2*b*N vertices:
# A_j,x ~ B_t,x*g for each dart (j, t, g).
#
# Left multiplication by h is an automorphism of the lift, so the diameter is
# checked by BFS from the 2b identity-fibre vertices only.
# b = 1 reproduces the bi-Cayley search; b >= 2 gives larger lifts.
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


def _unreached(b, N, T, invs, sig, gs, d, D):
    """Count (source, vertex) pairs at distance > D over the 2b identity-fibre sources."""
    out = [[] for _ in range(b)]   # out[j]: (t, g) for darts A_j -> B_t
    inn = [[] for _ in range(b)]   # inn[t]: (j, g^-1) for darts A_j -> B_t
    p = 0
    for i in range(d):
        for j in range(b):
            t = sig[i][j]
            g = gs[p]
            p += 1
            out[j].append((t, g))
            inn[t].append((j, invs[g]))

    bN = b * N
    V = 2 * bN
    total = 0
    for s in range(2 * b):
        src = s * N          # identity fibre of base vertex s (A_s or B_{s-b})
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < bN:
                    j, x = divmod(v, N)
                    row = T[x]
                    for t, g in out[j]:
                        w = bN + t * N + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    t, y = divmod(v - bN, N)
                    row = T[y]
                    for j, gi in inn[t]:
                        w = j * N + row[gi]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(b, N, T, invs, sig, d, D, rng, iters, deadline):
    """Simulated annealing over the d*b voltages to drive the unreached count to zero."""
    m = d * b
    gs = [rng.randrange(N) for _ in range(m)]
    cur = _unreached(b, N, T, invs, sig, gs, d, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 1.5 * (1.0 - it / iters))
        p = rng.randrange(m)
        c = rng.randrange(N)
        if c == gs[p]:
            continue
        old = gs[p]
        gs[p] = c
        v = _unreached(b, N, T, invs, sig, gs, d, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[p] = old
    return gs if cur == 0 else None


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N for base size b until one gives a valid voltage assignment."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        sig = [list(range(b))] + [rng.sample(range(b), b) for _ in range(d - 1)]
        gs = _anneal(b, N, T, invs, sig, d, D, rng, ITERS, deadline)
        if gs is not None:
            return T, sig, gs
    return None


def _edges(b, N, T, sig, gs, d):
    """Materialise the lift: vertices A_j,x = j*N+x and B_t,y = b*N + t*N + y."""
    edges = set()
    bN = b * N
    p = 0
    for i in range(d):
        for j in range(b):
            t = sig[i][j]
            g = gs[p]
            p += 1
            for x in range(N):
                edges.add((j * N + x, bN + t * N + T[x][g]))
    return [(a, c) for a, c in edges]


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

    moore = lib._moore_bound(d, D)

    # Round-robin over base sizes b. For each b, climb N upward starting just
    # above the current best order, so every success strictly improves.
    state = {}
    budget = {}
    for b in KS:
        state[b] = max(2, best_n // (2 * b) + 1)
        budget[b] = 0.3

    while time.monotonic() < deadline:
        active = False
        for b in KS:
            N = state[b]
            if 2 * b * N > moore:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            active = True
            res = _attempt(b, N, d, D, rng, min(deadline, now + budget[b]))
            if res is None:
                budget[b] = min(MAX_BUDGET, budget[b] * 1.4)
                continue
            T, sig, gs = res
            consider(2 * b * N, _edges(b, N, T, sig, gs, d))
            state[b] = N + 1
        if not active:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
