import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 3   # groups tried per (b, N) attempt
ITERS = 900                  # annealing steps per (group, dart matching) try
T_HOT = 3.0                  # initial annealing temperature (unreached-pair units)
T_COLD = 0.2                 # final annealing temperature
DUP_PENALTY = 6              # cost of a duplicated dart (same orbit pair and group element)
SPAN = 4                     # width of the (b >= 2) order window above the current best
B_MAX = 6                    # largest number of base vertices per side tried
BUDGET_START = 1.5           # seconds per attempt in the first pass
BUDGET_CAP = 6.0             # cap on per-attempt seconds as passes fail


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
# Multi-orbit voltage lifts over finite groups.
#
# New construction used here: instead of one orbit per side (a bi-Cayley graph),
# take b orbits per side. Vertices are A_{i,x} and B_{j,y} for i, j in 0..b-1 and
# x, y in G, |G| = N. A dart (i, j, g) adds the edges A_{i,x} -- B_{j, x*g} for
# every x in G. Every dart from orbit i gives A_{i,*} one edge, so the degree
# is d when each side has exactly d*b darts. The darts come from a random
# stub matching and are annealed over group elements and B-endpoint swaps.
#
# Left multiplication by G is an automorphism that acts regularly on each orbit,
# so the diameter test needs only 2b BFS runs, from A_{i,e} and B_{j,e}.
# The order is 2*b*N, which allows many more shapes than b = 1.
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


def _cost(N, b, D, T, invs, darts):
    """Number of unreached (source, vertex) pairs over the 2b orbit sources, plus duplicate penalty."""
    base = b * N
    V = 2 * base
    Aadj = [[] for _ in range(b)]
    Badj = [[] for _ in range(b)]
    keys = set()
    dup = 0
    for i, j, g in darts:
        key = (i, j, g)
        if key in keys:
            dup += 1
        else:
            keys.add(key)
        Aadj[i].append((j, g))
        Badj[j].append((i, invs[g]))
    total = DUP_PENALTY * dup
    sources = [i * N for i in range(b)] + [base + j * N for j in range(b)]
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        count = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < base:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in Aadj[i]:
                        v = base + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - base, N)
                    row = T[y]
                    for i, h in Badj[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(N, b, d, D, T, invs, rng, iters, deadline):
    """Anneal darts (i, j, g) so that the lift has diameter <= D. Return darts or None."""
    stubs = [i for i in range(b) for _ in range(d)]
    bstubs = stubs[:]
    rng.shuffle(bstubs)
    darts = [[stubs[k], bstubs[k], rng.randrange(N)] for k in range(len(stubs))]
    m = len(darts)
    cur = _cost(N, b, D, T, invs, darts)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        if rng.random() < 0.5:
            k = rng.randrange(m)
            old = darts[k][2]
            new = rng.randrange(N)
            if new == old:
                continue
            darts[k][2] = new
            v = _cost(N, b, D, T, invs, darts)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                darts[k][2] = old
        else:
            p = rng.randrange(m)
            q = rng.randrange(m)
            if darts[p][1] == darts[q][1]:
                continue
            darts[p][1], darts[q][1] = darts[q][1], darts[p][1]
            v = _cost(N, b, D, T, invs, darts)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                darts[p][1], darts[q][1] = darts[q][1], darts[p][1]
    return darts if cur == 0 else None


def _edges(N, b, T, darts):
    """Expand darts into the explicit edge list on 2*b*N vertices."""
    base = b * N
    E = []
    for i, j, g in darts:
        for x in range(N):
            E.append((i * N + x, base + j * N + T[x][g]))
    return E


def _attempt(N, b, d, D, rng, deadline):
    """Try groups of order N for a b-orbit lift. Return (n, edges) with diameter <= D, or None."""
    groups = _groups(N)
    if not groups:
        return None
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(N, b, d, D, T, invs, rng, ITERS, deadline)
        if darts is not None:
            return 2 * b * N, _edges(N, b, T, darts)
    return None


def _candidates(d, D, best_n, M):
    """(b, N) pairs whose lift order 2*b*N exceeds best_n. b = 1 uses the top of its window."""
    cands = []
    for b in range(1, B_MAX + 1):
        hi = M // (2 * b)
        lo = max(d + 1, best_n // (2 * b) + 1)
        if b == 1:
            start = max(lo, hi - 4)
            ns = range(start, hi + 1)
        else:
            ns = range(lo, min(hi, lo + SPAN) + 1)
        for N in ns:
            cands.append((b, N))
    return cands


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
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

    M = lib._moore_bound(d, D)
    budget = BUDGET_START
    while time.monotonic() < deadline:
        cands = _candidates(d, D, best_n, M)
        if not cands:
            break
        rng.shuffle(cands)
        success = False
        for b, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, b, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            consider(*res)
            success = True
            break
        if not success:
            budget = min(BUDGET_CAP, budget * 1.5)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
