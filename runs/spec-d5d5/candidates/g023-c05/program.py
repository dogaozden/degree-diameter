import itertools
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (b, N) attempt
ITERS = 800                   # annealing steps per (group, base layout) try
T_HOT = 2.0                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.2                  # final annealing temperature


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
# NEW: two-orbit voltage lifts over semidirect groups.
#
# Base multigraph on b "A" vertices and b "B" vertices. Each dart (i, j, g)
# joins A_{i,x} to B_{j, x*g} for every x in G. Left multiplication by G is an
# automorphism, so eccentricities need only one source per orbit: A_{i,e} and
# B_{j,e}, i.e. 2b BFS runs on a graph with 2bN vertices.
#
# For b = 2 the base multiplicity matrix is [[a, d-a], [d-a, a]], which has
# every row and column summing to d. Orders 4N can beat the b = 1 (2N) family.
# Vectorised BFS uses numpy on an explicit neighbour table.
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


def _mul_table(m, k, r):
    """Return (MulCol, invs): MulCol[g, x] = x*g and invs[g] = g^{-1}, for the group Z_m x|_r Z_k."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    Mul = np.array([[mul(x, g) for g in range(order)] for x in range(order)], dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    MulCol = np.ascontiguousarray(Mul.T)
    return MulCol, invs


def _layout(b, M):
    """Expand base multiplicity matrix M into darts (i, j), with per-row and per-column slot positions."""
    pairs = []
    for i in range(b):
        for j in range(b):
            pairs += [(i, j)] * M[i][j]
    posA, posB = [], []
    ca = [0] * b
    cb = [0] * b
    for (i, j) in pairs:
        posA.append(ca[i])
        ca[i] += 1
        posB.append(cb[j])
        cb[j] += 1
    return pairs, posA, posB


def _neighbors(b, N, d, pairs, posA, posB, gs, MulCol, invs):
    """Neighbour table of shape (2bN, d). A_{i,x} = i*N+x, B_{j,y} = b*N + j*N + y."""
    V = 2 * b * N
    nbr = np.empty((V, d), dtype=np.int64)
    base_B = b * N
    for t, (i, j) in enumerate(pairs):
        g = gs[t]
        nbr[i * N:(i + 1) * N, posA[t]] = base_B + j * N + MulCol[g]
        nbr[base_B + j * N: base_B + (j + 1) * N, posB[t]] = i * N + MulCol[invs[g]]
    return nbr


def _unreached(nbr, b, N, D):
    """Total number of (source, vertex) pairs not within distance D, over one source per orbit."""
    V = nbr.shape[0]
    sources = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    total = 0
    for s in sources:
        seen = np.zeros(V, dtype=bool)
        seen[s] = True
        fr = np.array([s], dtype=np.int64)
        cnt = 1
        for _ in range(D):
            nb = nbr[fr].ravel()
            nb = np.unique(nb[~seen[nb]])
            if nb.size == 0:
                break
            seen[nb] = True
            cnt += nb.size
            fr = nb
        total += V - cnt
    return total


def _random_darts(pairs, N, rng):
    """Random group elements for each dart, distinct within each (i, j) class so no parallel edges."""
    gs = [0] * len(pairs)
    classes = {}
    for t, p in enumerate(pairs):
        classes.setdefault(p, []).append(t)
    for p, ts in classes.items():
        if len(ts) > N:
            return None
        vals = rng.sample(range(N), len(ts))
        for t, v in zip(ts, vals):
            gs[t] = v
    return gs


def _anneal(b, N, d, D, pairs, posA, posB, MulCol, invs, rng, iters, deadline):
    """Simulated annealing over dart group elements to zero unreached pairs."""
    T = len(pairs)
    gs = _random_darts(pairs, N, rng)
    if gs is None:
        return None
    cur = _unreached(_neighbors(b, N, d, pairs, posA, posB, gs, MulCol, invs), b, N, D)
    for it in range(iters):
        if cur == 0:
            return gs
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        t = rng.randrange(T)
        c = rng.randrange(N)
        i, j = pairs[t]
        if any(gs[s] == c for s in range(T) if s != t and pairs[s] == (i, j)):
            continue
        old = gs[t]
        gs[t] = c
        v = _unreached(_neighbors(b, N, d, pairs, posA, posB, gs, MulCol, invs), b, N, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[t] = old
    if cur == 0:
        return gs
    return None


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N for a b-orbit base layout; return a neighbour table or None."""
    if b == 1:
        M = [[d]]
    else:
        a = rng.randint(1, d - 1)
        M = [[a, d - a], [d - a, a]]
    pairs, posA, posB = _layout(b, M)
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        MulCol, invs = _mul_table(m, k, r)
        gs = _anneal(b, N, d, D, pairs, posA, posB, MulCol, invs, rng, ITERS, deadline)
        if gs is not None:
            return _neighbors(b, N, d, pairs, posA, posB, gs, MulCol, invs)
    return None


def _edges_from(nbr):
    """Return (n, edges) from a neighbour table, de-duplicated."""
    V, d = nbr.shape
    src = np.repeat(np.arange(V, dtype=np.int64), d)
    dst = nbr.ravel()
    lo = np.minimum(src, dst)
    hi = np.maximum(src, dst)
    edges = sorted(set(zip(lo.tolist(), hi.tolist())))
    return V, edges


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

    bound = lib._moore_bound(d, D)
    # Only orders in the upper part of the Moore range are worth searching.
    floor_tot = max(best_n + 1, (bound * 45) // 100)
    pool = []
    for b in (2, 1):
        for N in range(d, bound // (2 * b) + 1):
            tot = 2 * b * N
            if floor_tot <= tot <= bound:
                pool.append((tot, b, N))
    pool.sort()

    budget = 0.15
    while pool and time.monotonic() < deadline:
        for tot, b, N in list(pool):
            if tot <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            nbr = _attempt(b, N, d, D, rng, att_deadline)
            if nbr is None:
                continue
            V, edges = _edges_from(nbr)
            consider(V, edges)
            pool = [p for p in pool if p[0] > best_n and p != (tot, b, N)]
        budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
