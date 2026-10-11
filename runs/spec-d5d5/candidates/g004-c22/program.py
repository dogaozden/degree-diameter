import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (base size, order) attempt
ITERS = 350                   # annealing steps per (group, base matrix) try
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature


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
# Group enumeration (semidirect products Z_m x|_r Z_k of order N).
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


# ----------------------------------------------------------------------------
# NEW IDEA: multi-class voltage lifts with a permutation-sum base matrix.
#
# A base bipartite multigraph has `a` classes A_0..A_{a-1} and `a` classes
# B_0..B_{a-1}, and an a x a count matrix M with all row and column sums d.
# M is drawn as a sum of d random permutation matrices, so every such M is
# automatically d-regular on both sides. Each cell (i, j) carries M[i][j]
# distinct group elements ("darts"). The lift has vertices A_{i,x}, B_{j,y}
# for x, y in G (|G| = N) and edges A_{i,x} -- B_{j, x*g} for each dart g
# in cell (i, j). Total order 2aN, degree d.
#
# Left multiplication by G is an automorphism, so eccentricities are constant
# on each class. Checking BFS from the identity of each of the 2a classes
# therefore decides the diameter. Simulated annealing moves single darts to
# reduce the number of unreached (source, vertex) pairs.
#
# Parent code only searched a = 1 (bi-Cayley graphs, 2N vertices). Larger a
# gives order 2aN with the same degree, so it can exceed the record.
# ----------------------------------------------------------------------------

def _random_base(a, d, rng):
    """Count matrix as a sum of d random permutation matrices: all row and column sums equal d."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for i in range(a):
            M[i][p[i]] += 1
    return M


def _base_connected(a, M):
    """True if the base bipartite multigraph with counts M is connected."""
    par = list(range(2 * a))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for i in range(a):
        for j in range(a):
            if M[i][j]:
                par[find(i)] = find(a + j)
    r = find(0)
    return all(find(v) == r for v in range(2 * a))


def _cells(M, N, rng):
    """Random distinct darts for each nonzero cell: list of [i, j, [g, ...]]."""
    cells = []
    for i, row in enumerate(M):
        for j, c in enumerate(row):
            if c:
                cells.append([i, j, rng.sample(range(N), c)])
    return cells


def _adjacency(a, N, T, cells):
    """Adjacency lists on 2aN vertices: A_{i,x} = i*N + x, B_{j,y} = a*N + j*N + y."""
    off = a * N
    adj = [[] for _ in range(2 * a * N)]
    for i, j, gs in cells:
        ia = i * N
        jb = off + j * N
        for g in gs:
            for x in range(N):
                y = T[x][g]
                adj[ia + x].append(jb + y)
                adj[jb + y].append(ia + x)
    return adj


def _unreached(a, N, adj, D):
    """Count (source, vertex) pairs not within distance D, for the identity of every class."""
    n = 2 * a * N
    sources = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    total = 0
    for src in sources:
        seen = bytearray(n)
        seen[src] = 1
        count = 1
        frontier = [src]
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
        total += n - count
    return total


def _anneal(a, N, T, M, D, rng, iters, deadline):
    """Anneal the darts of a fixed base matrix M until every class pair is within D."""
    cells = _cells(M, N, rng)
    cur = _unreached(a, N, _adjacency(a, N, T, cells), D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        cell = cells[rng.randrange(len(cells))]
        k = rng.randrange(len(cell[2]))
        c = rng.randrange(N)
        if c in cell[2]:
            continue
        old = cell[2][k]
        cell[2][k] = c
        v = _unreached(a, N, _adjacency(a, N, T, cells), D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            cell[2][k] = old
    return cells if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N with random connected base matrices until one lift works."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        M = None
        for _ in range(50):
            cand = _random_base(a, d, rng)
            if _base_connected(a, cand):
                M = cand
                break
        if M is None:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        cells = _anneal(a, N, T, M, D, rng, ITERS, deadline)
        if cells is not None:
            return T, cells
    return None


def _edges(a, N, T, cells):
    """Edge list of the lift; each (cell, dart, x) gives a distinct edge."""
    off = a * N
    edges = []
    for i, j, gs in cells:
        for g in gs:
            for x in range(N):
                edges.append((i * N + x, off + j * N + T[x][g]))
    return 2 * a * N, edges


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
    families = [a for a in (2, 3, 4, 1) if 2 * a * d <= moore]

    budget = 0.5
    while time.monotonic() < deadline and families:
        progressed = False
        for a in families:
            N = max(d, best_n // (2 * a) + 1)   # strictly beat the current best
            if 2 * a * N > moore:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(a, N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, cells = res
            n, e = _edges(a, N, T, cells)
            consider(n, e)
            progressed = True
            break
        if not progressed:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
