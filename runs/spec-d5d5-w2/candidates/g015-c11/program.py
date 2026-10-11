import math
import random
import time

import lib

ITERS = 1500              # annealing steps per (group, base size) try
T_HOT = 3.0               # initial temperature (unreached-pair units)
T_COLD = 0.2              # final temperature
MAX_GROUPS = 10           # groups tried per (b, N) attempt
BASES = (1, 2, 3, 4)      # base vertices per side for the multi-base voltage lift
NCAP = 400                # cap on group order (keeps multiplication tables small)
DUP_PENALTY = 30          # cost per duplicated dart (would create a parallel edge)
BUDGET_START = 1.5        # seconds per (b, N) attempt in the first pass
BUDGET_CAP = 6.0          # cap on per-attempt seconds as passes fail
SPAN_START = 6            # search N in [top - span, top] first; widen when stuck


# ----------------------------------------------------------------------------
# Baseline families (cheap, always checked with lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    import itertools
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
    for q in range(min(d - 1, 4), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW: multi-base voltage lifts over semidirect groups.
#
# Base multigraph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}, with
# d darts leaving each A_i and d darts entering each B_j (a d-regular bipartite
# multigraph on the base). A dart (i, j, a) with a in G gives edges
#     A(i, x) -- B(j, x*a)     for every x in G.
# Left multiplication by G is an automorphism, so every vertex of a fibre has
# the same eccentricity as A(i, e) or B(j, e). Only 2b BFS sources are needed.
# Parallel darts with identical (i, j, a) would create duplicate edges, so
# they are penalised. Moves are voltage changes and swaps of B-endpoints
# (both keep regularity). Annealing drives unreached pairs to zero.
# Order of the lift is 2 * b * N, so b > 1 gives many more orders than b = 1.
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


def _cost(b, N, D, T, invs, darts):
    """Unreached (source, vertex) pairs for the 2b base sources, plus duplicate penalty."""
    bN = b * N
    V = 2 * bN
    outA = [[] for _ in range(b)]
    inB = [[] for _ in range(b)]
    for i, j, a in darts:
        outA[i].append((j, a))
        inB[j].append((i, invs[a]))
    dup = len(darts) - len(set(darts))
    sources = [i * N for i in range(b)] + [bN + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, a in outA[i]:
                        v = bN + j * N + row[a]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bN, N)
                    row = T[y]
                    for i, ia in inB[j]:
                        v = i * N + row[ia]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total + DUP_PENALTY * dup


def _init(b, d, N, rng):
    """Random d-regular base multigraph on b+b vertices with random voltages."""
    A = [i for i in range(b) for _ in range(d)]
    B = A[:]
    rng.shuffle(B)
    return [(A[t], B[t], rng.randrange(N)) for t in range(len(A))]


def _anneal(b, N, d, D, T, invs, rng, deadline):
    """Anneal darts to zero unreached pairs and zero duplicates; None on failure."""
    darts = _init(b, d, N, rng)
    cur = _cost(b, N, D, T, invs, darts)
    for step in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (step / ITERS)
        new = list(darts)
        if rng.random() < 0.5:
            t = rng.randrange(len(new))
            i, j, _ = new[t]
            new[t] = (i, j, rng.randrange(N))
        else:
            t, u = rng.sample(range(len(new)), 2)
            it_, jt, at = new[t]
            iu, ju, au = new[u]
            if jt == ju:
                continue
            new[t] = (it_, ju, at)
            new[u] = (iu, jt, au)
        v = _cost(b, N, D, T, invs, new)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N for base size b until a valid voltage assignment appears."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(b, N, d, D, T, invs, rng, deadline)
        if darts is not None:
            return darts, T
    return None


def _lift(b, N, T, darts):
    """Expand base darts over the group into an explicit (n, edges)."""
    bN = b * N
    edges = []
    for i, j, a in darts:
        for x in range(N):
            edges.append((i * N + x, bN + j * N + T[x][a]))
    return 2 * bN, edges


# ----------------------------------------------------------------------------

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

    # Calibration case: incidence graph of PG(2, d-1) meets the Moore bound.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 1:
        consider(2, [(0, 1)])
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

    Moore = lib._moore_bound(d, D)
    span = SPAN_START
    budget = BUDGET_START

    while time.monotonic() < deadline:
        cands = []
        for b in BASES:
            top = min(Moore // (2 * b), NCAP)
            lo = max(d, best_n // (2 * b) + 1, top - span)
            for N in range(lo, top + 1):
                cands.append((b, N))
        if not cands:
            break
        rng.shuffle(cands)
        success = False
        for b, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(b, N, d, D, rng, att_deadline)
            if res is None:
                continue
            darts, T = res
            n, edges = _lift(b, N, T, darts)
            consider(n, edges)
            success = True
            break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            else:
                span += 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
