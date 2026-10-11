import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 10   # groups tried per (N, k) attempt
ITERS = 300                   # annealing steps per attempt
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
BUDGET_START = 4.0            # seconds per attempt at the start
BUDGET_CAP = 10.0             # cap on per-attempt seconds
PRODUCT_MOVE_PROB = 0.5       # chance a move proposes a product of two set elements


# ----------------------------------------------------------------------------
# Baseline families (always validated before being returned).
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
# Multi-orbit bi-Cayley (group lift) search.
#
# Group G = Z_m x| Z_k of order N, coded as integers with identity 0.
# k orbits on each side: A_i(x) for i < k and B_j(y) for j < k, 2kN vertices.
# A dart g in the (i, j) cell gives edges A_i(x) -- B_j(x*g) for all x in G.
# Each A_i has degree d (row sum d), each B_j has degree d (column sum d).
# Left translation by G is an automorphism, so the diameter is checked by BFS
# from one source per orbit (2k sources). The k = 1 case is the classic
# bi-Cayley search; k = 2 is the new, larger-base family.
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


def _table(m, k, r):
    """Multiplication table T[x][y] for Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    N = m * k
    powers = [pow(r, b, m) for b in range(k)]
    T = [[0] * N for _ in range(N)]
    for x in range(N):
        a, b = divmod(x, k)
        row = T[x]
        pb = powers[b]
        for y in range(N):
            c, e = divmod(y, k)
            row[y] = ((a + pb * c) % m) * k + (b + e) % k
    return T


def _unreached(N, k, T, darts, D):
    """Count (source, vertex) pairs not within distance D, over one source per orbit."""
    V = 2 * k * N
    adj = [[] for _ in range(V)]
    for i in range(k):
        for j in range(k):
            base_b = (k + j) * N
            for g in darts[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = base_b + T[x][g]
                    adj[a].append(b)
                    adj[b].append(a)
    sources = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        count = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(N, k, T, darts, D, rng, iters, deadline):
    """Anneal the dart cells to zero unreached pairs. The identity at cell (0,0) is fixed (WLOG)."""
    positions = [(i, j, p)
                 for i in range(k) for j in range(k)
                 for p in range(len(darts[i][j]))
                 if not (i == 0 and j == 0 and p == 0)]
    cur = _unreached(N, k, T, darts, D)
    if not positions:
        return cur == 0
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j, p = rng.choice(positions)
        cell = darts[i][j]
        if rng.random() < PRODUCT_MOVE_PROB:
            pool = [g for ii in range(k) for jj in range(k) for g in darts[ii][jj]]
            c = T[rng.choice(pool)][rng.choice(pool)]
        else:
            c = rng.randrange(N)
        if c in cell:
            continue
        old = cell[p]
        cell[p] = c
        v = _unreached(N, k, T, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            cell[p] = old
    return cur == 0


def _attempt(N, k, d, D, rng, deadline):
    """Try groups of order N for k orbits per side; return (T, darts) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    if k == 1:
        counts = [[d]]
    else:
        a = rng.randint(1, d - 1)
        counts = [[a, d - a], [d - a, a]]
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        T = _table(m, kk, r)
        darts = [[None] * k for _ in range(k)]
        for i in range(k):
            for j in range(k):
                c = counts[i][j]
                if i == 0 and j == 0:
                    darts[i][j] = [0] + rng.sample(range(1, N), c - 1)
                else:
                    darts[i][j] = rng.sample(range(1, N), c)
        if _anneal(N, k, T, darts, D, rng, ITERS, deadline):
            return T, darts
    return None


def _edges(N, k, T, darts):
    """Expand a found (T, darts) into the edge list on 2kN vertices."""
    out = []
    for i in range(k):
        for j in range(k):
            for g in darts[i][j]:
                for x in range(N):
                    out.append((i * N + x, (k + j) * N + T[x][g]))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_total = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget_total
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

    try:
        while time.monotonic() < deadline:
            options = []
            for k in (1, 2):
                if k == 2 and d < 2:
                    continue
                hi = M // (2 * k)
                lo = max(d + 1, best_n // (2 * k) + 1)
                if lo <= hi:
                    options.append((k, lo, hi))
            if not options:
                break
            k, lo, hi = options[rng.randrange(len(options))]
            span = hi - lo
            # Bias toward the top of the window; occasionally sample lower.
            N = hi - int((rng.random() ** 2) * (span + 1))
            N = max(lo, min(hi, N))

            att_deadline = min(deadline, time.monotonic() + budget)
            res = _attempt(N, k, d, D, rng, att_deadline)
            if res is not None:
                T, darts = res
                consider(2 * k * N, _edges(N, k, T, darts))
            else:
                budget = min(BUDGET_CAP, budget * 1.1)
    except Exception:
        pass  # keep whatever validated graph we already have

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
