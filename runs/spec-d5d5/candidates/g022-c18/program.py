import itertools
import math
import random
import time

import lib

ITERS = 300                  # annealing steps per (group, base matrix) try
T_HOT = 1.5                  # initial temperature (in unreached-pair units)
T_COLD = 0.15                # final temperature
GROUPS_PER_ATTEMPT = 8       # groups tried for one (a, N) attempt
ATTEMPT_BUDGET = 6.0         # seconds per (a, N) attempt


# ----------------------------------------------------------------------------
# Baseline families (kept from the parent; always validated before use).
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
# NEW: multi-orbit bi-Cayley (2-orbit / 3-orbit voltage lifts) over groups.
#
# Base graph: a "A-orbits" and a "B-orbits", each orbit a copy of G (|G| = N).
# A base matrix M (a x a, row and column sums d) says how many darts join
# A_i to B_j. Each cell with M[i][j] = k gets k distinct group elements g, and
# the lift joins A_i,x to B_j,x*g. The result is d-regular, bipartite, with
# 2*a*N vertices. Left multiplication by G is an automorphism, and it acts
# transitively on each orbit, so the eccentricities are decided by 2a sources
# (one per orbit). Parent searched only the a = 1 case.
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


def _perm_sum_matrix(a, d, rng):
    """Random a x a nonnegative integer matrix with all row and column sums d (sum of d permutations)."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for i in range(a):
            M[i][p[i]] += 1
    return M


def _cost(a, N, D, T, invs, cells, vals):
    """Number of (source, vertex) pairs at distance > D, sources = one vertex per orbit."""
    out = [[] for _ in range(a)]   # A_i -> list of (j, g)
    inn = [[] for _ in range(a)]   # B_j -> list of (i, g^-1)
    for (i, j, _), gl in zip(cells, vals):
        for g in gl:
            out[i].append((j, g))
            inn[j].append((i, invs[g]))
    AN = a * N
    V = 2 * AN
    total = 0
    sources = [i * N for i in range(a)] + [AN + j * N for j in range(a)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < AN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in out[i]:
                        v = AN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - AN, N)
                    row = T[y]
                    for i, h in inn[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(a, N, T, invs, d, D, rng, deadline):
    """Anneal the dart labels of one random base matrix to zero unreached pairs."""
    M = _perm_sum_matrix(a, d, rng)
    cells = [(i, j, M[i][j]) for i in range(a) for j in range(a) if M[i][j] > 0]
    vals = [rng.sample(range(N), k) for _, _, k in cells]
    cur = _cost(a, N, D, T, invs, cells, vals)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        c = rng.randrange(len(cells))
        pos = rng.randrange(cells[c][2])
        new = rng.randrange(N)
        if new in vals[c]:
            continue
        old = vals[c][pos]
        vals[c][pos] = new
        v = _cost(a, N, D, T, invs, cells, vals)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vals[c][pos] = old
    if cur == 0:
        return cells, vals
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for a orbits per side; return (cells, vals, T) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        res = _anneal(a, N, T, invs, d, D, rng, deadline)
        if res is not None:
            cells, vals = res
            return cells, vals, T
    return None


def _edges_from(a, N, cells, vals, T):
    """Expand the base-matrix lift into an explicit edge list."""
    edges = []
    AN = a * N
    for (i, j, _), gl in zip(cells, vals):
        for g in gl:
            for x in range(N):
                edges.append((i * N + x, AN + j * N + T[x][g]))
    return 2 * AN, edges


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

    Mb = lib._moore_bound(d, D)
    fails = 0
    while time.monotonic() < deadline:
        feasible = [a for a in (1, 2, 3) if best_n // (2 * a) + 1 <= Mb // (2 * a)]
        if not feasible:
            break
        a = rng.choice([x for x in (1, 2, 2, 2, 3) if x in feasible])
        Nmax = Mb // (2 * a)
        Nmin = best_n // (2 * a) + 1
        spread = min(Nmax - Nmin + 1, 1 + fails // 3)
        N = Nmin + rng.randrange(spread)
        att_deadline = min(deadline, time.monotonic() + ATTEMPT_BUDGET)
        res = _attempt(a, N, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            continue
        cells, vals, T = res
        n, e = _edges_from(a, N, cells, vals, T)
        consider(n, e)
        fails = 0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
