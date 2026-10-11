import itertools
import math
import random
import time

import lib

MAX_GROUPS = 6        # groups tried per attempt
ITERS = 400           # annealing steps per (group, base-structure) try
T_HOT = 2.0           # initial annealing temperature (in unreached-pair units)
T_COLD = 0.2          # final annealing temperature
BUDGET_START = 2.0    # seconds per attempt, first pass
BUDGET_CAP = 8.0      # cap on per-attempt seconds as failures accumulate


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
# Multi-base voltage lifts over groups of order N.
#
# Base graph: a vertices on side A, a on side B, and d "layers". Layer k is a
# permutation sigma_k of range(a) with a voltage v_{k,i} in G, giving edges
#     A_{i,x} -- B_{sigma_k(i), x * v_{k,i}}   for all x in G.
# Every A and B vertex has degree d. Left multiplication by G is an
# automorphism, so the diameter is decided by BFS from the 2a sources
# A_{i,e} and B_{j,e} (vertex index t*N for t in range(2a)).
#
# a = 1 is the bi-Cayley family. a >= 2 is the new, larger base family.
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


def _mul_table(mul, N):
    return [[mul(x, y) for y in range(N)] for x in range(N)]


def _cost(a, N, d, D, perms, volt, MT):
    """Total unreached (source, vertex) pairs over the 2a base sources."""
    n = 2 * a * N
    adj = [[] for _ in range(n)]
    for k in range(d):
        pk = perms[k]
        vk = volt[k]
        for i in range(a):
            j = pk[i]
            v = vk[i]
            ai = i * N
            bj = (a + j) * N
            for x in range(N):
                b = bj + MT[x][v]
                adj[ai + x].append(b)
                adj[b].append(ai + x)
    total = 0
    for t in range(2 * a):
        src = t * N
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _anneal(a, N, MT, d, D, rng, iters, deadline):
    """Simulated annealing over layer permutations and voltages to zero unreached pairs."""
    perms = [rng.sample(range(a), a) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(a)] for _ in range(d)]
    cur = _cost(a, N, d, D, perms, volt, MT)
    for it in range(iters):
        if cur == 0:
            return perms, volt
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        np_ = [p[:] for p in perms]
        nv = [r[:] for r in volt]
        k = rng.randrange(d)
        if a > 1 and rng.random() < 0.2:
            i1, i2 = rng.sample(range(a), 2)
            np_[k][i1], np_[k][i2] = np_[k][i2], np_[k][i1]
        else:
            i = rng.randrange(a)
            nv[k][i] = rng.randrange(N)
        v = _cost(a, N, d, D, np_, nv, MT)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            perms, volt, cur = np_, nv, v
    if cur == 0:
        return perms, volt
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for base size a until one yields diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        order, mul, _inv = lib.semidirect_group(m, k, r)
        MT = _mul_table(mul, N)
        res = _anneal(a, N, MT, d, D, rng, ITERS, deadline)
        if res is not None:
            perms, volt = res
            return a, N, MT, perms, volt
    return None


def _edges(a, N, d, perms, volt, MT):
    """Edge list of the lift, deduplicated. A-vertices are 0..aN-1, B-vertices aN..2aN-1."""
    E = set()
    for k in range(d):
        for i in range(a):
            j = perms[k][i]
            v = volt[k][i]
            for x in range(N):
                E.add((i * N + x, (a + j) * N + MT[x][v]))
    return sorted(E)


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

    # Record-matching constructions for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except ValueError:
            pass

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

    moore = lib._moore_bound(d, D)
    win = 2
    failures = 0
    budget = BUDGET_START

    while time.monotonic() < deadline:
        choices = []
        for a in (1, 2, 3):
            lo = best_n // (2 * a) + 1
            hi = moore // (2 * a)
            if lo <= hi:
                choices.append((a, lo, hi))
        if not choices:
            break
        a, lo, hi = rng.choice(choices)
        N = rng.randint(lo, min(hi, lo + win))
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(a, N, d, D, rng, att_deadline)
        if res is None:
            failures += 1
            if failures % 4 == 0:
                budget = min(BUDGET_CAP, budget * 1.5)
                win += 1
            continue
        a, N, MT, perms, volt = res
        consider(2 * a * N, _edges(a, N, d, perms, volt, MT))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
