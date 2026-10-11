import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 10   # groups tried per (orbits k, order N) attempt
ITERS = 700                   # annealing steps per attempt
T_HOT = 2.0                   # initial temperature (unreached-pair units)
T_COLD = 0.2                  # final temperature
BUDGET_START = 0.5            # seconds per candidate in the first pass
BUDGET_CAP = 4.0              # cap on per-candidate seconds
WINDOW = 30                   # vertex-count window above the lower edge to search first
LO_RATIO = 0.48               # lower edge of the search window, as a fraction of the Moore bound
LO_DECAY = 0.97               # widen the window downward after a failed pass
MAX_ORBITS = 8                # largest number of base vertices per side tried


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
# Group enumeration: semidirect products Z_m x|_r Z_k of order N.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, kk, r) with m*kk = N, giving Z_m x|_r Z_kk."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


# ----------------------------------------------------------------------------
# New construction: multi-orbit group lifts ("k-orbit bi-Cayley graphs").
#
# Take a group G of order N and k orbits on each side. Vertices are
# A_{i,x} and B_{j,y} for x, y in G and i, j < k. A dart (i, j, g) adds the
# edges A_{i,x} -- B_{j, x g} for all x. Each A-orbit carries exactly d darts
# and each B-orbit receives exactly d darts, so the graph is d-regular on
# 2kN vertices. Left multiplication by G is an automorphism, so the
# eccentricities from the k A-orbit identities and k B-orbit identities
# decide the diameter. k = 1 is the usual bi-Cayley search.
# ----------------------------------------------------------------------------

def _lift_cost(k, N, T, invs, darts, D):
    """Count (source, vertex) pairs not within distance D, over one source per orbit."""
    kN = k * N
    total = 2 * kN
    Aout = [[] for _ in range(k)]
    Bin = [[] for _ in range(k)]
    for i, j, g in darts:
        Aout[i].append((j, g))
        Bin[j].append((i, invs[g]))
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    cost = 0
    for s in sources:
        seen = bytearray(total)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in Aout[i]:
                        v = kN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, hinv in Bin[j]:
                        v = i * N + row[hinv]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        cost += total - count
    return cost


def _anneal_lift(k, N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over the dart set to drive the unreached-pair count to zero.

    Moves: re-voltage one dart, or swap the B-orbit targets of two darts.
    Both keep every A-orbit and every B-orbit at exactly d darts.
    """
    A = [i for i in range(k) for _ in range(d)]
    B = A[:]
    rng.shuffle(B)
    darts = [(A[t], B[t], rng.randrange(N)) for t in range(len(A))]
    for _ in range(10000):
        if len(set(darts)) == len(darts):
            break
        t = rng.randrange(len(darts))
        i, j, _g = darts[t]
        darts[t] = (i, j, rng.randrange(N))
    else:
        return None
    cur = _lift_cost(k, N, T, invs, darts, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        new = darts[:]
        if rng.random() < 0.5:
            t = rng.randrange(len(new))
            i, j, _g = new[t]
            new[t] = (i, j, rng.randrange(N))
        else:
            t1, t2 = rng.sample(range(len(new)), 2)
            i1, j1, g1 = new[t1]
            i2, j2, g2 = new[t2]
            if j1 == j2:
                continue
            new[t1] = (i1, j2, g1)
            new[t2] = (i2, j1, g2)
        if len(set(new)) != len(new):
            continue
        v = _lift_cost(k, N, T, invs, new, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N for k orbits until one yields a valid dart set."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal_lift(k, N, T, invs, d, D, rng, ITERS, deadline)
        if darts is not None:
            return darts, T
    return None


def _lift_edges(k, N, T, darts):
    """Expand darts into the explicit edge list (A vertices first, then B vertices)."""
    kN = k * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, kN + j * N + T[x][g]))
    return edges


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
    ratio = LO_RATIO
    budget = BUDGET_START

    while time.monotonic() < deadline:
        lo = max(best_n + 2, int(ratio * moore))
        hi = min(moore, lo + WINDOW)
        cands = []
        for k in range(1, MAX_ORBITS + 1):
            Nlo = max(d, lo // (2 * k))
            Nhi = hi // (2 * k)
            for N in range(Nlo, Nhi + 1):
                n = 2 * k * N
                if lo <= n <= hi:
                    cands.append((n, k, N))
        rng.shuffle(cands)
        cands.sort(key=lambda c: c[0])   # easiest (smallest) orders first

        success = False
        for n, k, N in cands:
            if n <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(k, N, d, D, rng, att_deadline)
            if res is None:
                continue
            darts, T = res
            consider(n, _lift_edges(k, N, T, darts))
            success = True
            break

        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            else:
                ratio *= LO_DECAY   # widen the window downward once budgets are maxed

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
