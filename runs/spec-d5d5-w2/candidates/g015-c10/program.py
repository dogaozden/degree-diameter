import itertools
import math
import random
import time

import lib

# Two-orbit bi-Cayley search (new in this version).
# A base graph with b orbits on each side is lifted by a finite group G of order N.
# Vertices are A(i, x) and B(j, y) for orbit indices i, j < b and x, y in G, so the
# order is 2*b*N. Each base dart (i, j, g) contributes edges A(i, x) -- B(j, x*g).
# The degree split c[i][j] (how many darts go from orbit i to orbit j) is chosen so
# every vertex has degree d. Left multiplication by G is an automorphism, so the
# diameter check only needs BFS from the 2*b base vertices at the identity. The
# annealing cost is the total number of unreached (source, vertex) pairs over those sources.

ITERS = 500
T_HOT = 2.0
T_COLD = 0.2
MAX_GROUPS = 10
BUDGET_START = 1.0
BUDGET_CAP = 4.0
P_TWO_ORBIT = 0.6


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Two-orbit bi-Cayley search over semidirect products Z_m x| Z_k.
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


def _cmat(b, d):
    """Degree split: c[i][j] darts from orbit i to orbit j, with every row and column summing to d."""
    if b == 1:
        return [[d]]
    a = (d + 1) // 2
    return [[a, d - a], [d - a, a]]


def _lists(b, gs, invs):
    """Per-orbit neighbour lists: dA[i] holds (j, g) and dB[j] holds (i, g^-1)."""
    dA = [[] for _ in range(b)]
    dB = [[] for _ in range(b)]
    for i in range(b):
        for j in range(b):
            for g in gs[i][j]:
                dA[i].append((j, g))
                dB[j].append((i, invs[g]))
    return dA, dB


def _cost(N, b, T, dA, dB, D):
    """Total unreached (source, vertex) pairs over the 2*b base sources at the identity."""
    bn = b * N
    tot = 2 * bn
    total = 0
    sources = [i * N for i in range(b)] + [bn + j * N for j in range(b)]
    for src in sources:
        seen = bytearray(tot)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bn:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in dA[i]:
                        v = bn + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bn, N)
                    row = T[y]
                    for i, h in dB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += tot - count
    return total


def _anneal(N, b, T, invs, cmat, rng, D, deadline):
    """Anneal the dart group elements so that the cost reaches zero."""
    pairs = [(i, j) for i in range(b) for j in range(b) if cmat[i][j] > 0]
    gs = [[[] for _ in range(b)] for _ in range(b)]
    for i, j in pairs:
        gs[i][j] = rng.sample(range(N), cmat[i][j])
    dA, dB = _lists(b, gs, invs)
    cur = _cost(N, b, T, dA, dB, D)
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        i, j = pairs[rng.randrange(len(pairs))]
        lst = gs[i][j]
        k = rng.randrange(len(lst))
        g_new = rng.randrange(N)
        if g_new in lst:
            continue
        old = lst[k]
        lst[k] = g_new
        dA, dB = _lists(b, gs, invs)
        v = _cost(N, b, T, dA, dB, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            lst[k] = old
    if cur == 0:
        return gs
    return None


def _attempt(N, b, cmat, d, D, rng, deadline):
    """Try groups of order N until one yields a valid two-orbit lift, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        gs = _anneal(N, b, T, invs, cmat, rng, D, deadline)
        if gs is not None:
            return T, invs, gs
    return None


def _edges(N, b, T, gs):
    """Expand the found dart set into an explicit graph with 2*b*N vertices."""
    bn = b * N
    edges = []
    for i in range(b):
        for j in range(b):
            for g in gs[i][j]:
                for x in range(N):
                    edges.append((i * N + x, bn + j * N + T[x][g]))
    return 2 * bn, edges


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

    moore = lib.moore_bound(d, D)
    Nmax = {1: moore // 2, 2: moore // 4}   # order is 2*b*N
    windows = {1: 3, 2: 3}
    budget = BUDGET_START

    while time.monotonic() < deadline:
        feasible = [bb for bb in (1, 2)
                    if max(d + 1, best_n // (2 * bb) + 1) <= Nmax[bb]]
        if not feasible:
            break
        if 2 in feasible and (1 not in feasible or rng.random() < P_TWO_ORBIT):
            b = 2
        else:
            b = 1
        lo = max(d + 1, best_n // (2 * b) + 1)
        hi = min(Nmax[b], lo + windows[b])
        N = rng.randint(lo, hi)
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(N, b, _cmat(b, d), d, D, rng, att_deadline)
        if res is None:
            windows[b] = int(windows[b] * 1.25) + 1
            budget = min(BUDGET_CAP, budget * 1.1)
        else:
            T, invs, gs = res
            n, edges = _edges(N, b, T, gs)
            consider(n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
