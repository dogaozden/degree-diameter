import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 10   # groups tried per (base size, order) attempt
ITERS = 500                   # annealing steps per (group, base matrix) try
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
MAX_BASE = 4                  # largest base size b (b vertices per side) tried
WINDOW = 6                    # candidate orders per base size above the current best


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
# New helper: random base multigraph as a sum of d permutation matrices.
#
# A b-vertex base (b on each side) with every vertex of degree d is a d-regular
# bipartite multigraph on b + b vertices. Summing d random permutation matrices
# gives exactly such a multigraph (row and column sums both d). We keep only
# choices whose base graph is connected, so that a lift can be connected.
# ----------------------------------------------------------------------------

def _sample_base(b, d, rng):
    """Return a b x b nonnegative integer matrix with row/col sums d and connected base, or None."""
    for _ in range(30):
        M = [[0] * b for _ in range(b)]
        for _ in range(d):
            p = list(range(b))
            rng.shuffle(p)
            for i in range(b):
                M[i][p[i]] += 1
        parent = list(range(2 * b))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for i in range(b):
            for j in range(b):
                if M[i][j]:
                    parent[find(i)] = find(b + j)
        root = find(0)
        if all(find(v) == root for v in range(2 * b)):
            return M
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over a semidirect product Z_m x|_r Z_k of order N.
#
# Base graph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}. A dart
# (i, j, g) gives edges A(i, x) -- B(j, x*g) for every x in G. Left
# multiplication by G is an automorphism, so every vertex A(i, x) is equivalent
# to A(i, e), and similarly for B. Hence the diameter check only needs BFS from
# the 2b sources A(i, e) and B(j, e).
#
# Vertex ids: A(i, x) = i*N + x, B(j, y) = b*N + j*N + y.
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


def _tables(b, darts, invs):
    """Adjacency tables: dout[i] = [(j, g)], din[j] = [(i, g^-1)]."""
    dout = [[] for _ in range(b)]
    din = [[] for _ in range(b)]
    for i, j, g in darts:
        dout[i].append((j, g))
        din[j].append((i, invs[g]))
    return dout, din


def _unreached(b, N, T, dout, din, D):
    """Count (source, vertex) pairs not within distance D, over all 2b base sources."""
    BN = b * N
    full = 2 * BN
    total = 0
    sources = [i * N for i in range(b)] + [BN + j * N for j in range(b)]
    for src in sources:
        seen = bytearray(full)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < BN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in dout[i]:
                        v = BN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - BN, N)
                    row = T[y]
                    for i, h in din[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += full - count
    return total


def _anneal(b, N, T, invs, d, D, M, rng, iters, deadline):
    """Anneal dart voltages for base matrix M until every source reaches all within D.

    Darts between the same base pair (i, j) get pairwise distinct voltages, so the
    lift is simple. Moves change one voltage; uphill moves are accepted with a
    temperature that decays geometrically from T_HOT to T_COLD.
    """
    darts = []
    for i in range(b):
        for j in range(b):
            used = set()
            for _ in range(M[i][j]):
                g = rng.randrange(N)
                while g in used:
                    g = rng.randrange(N)
                used.add(g)
                darts.append([i, j, g])
    dout, din = _tables(b, darts, invs)
    cur = _unreached(b, N, T, dout, din, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        k = rng.randrange(len(darts))
        i, j, old = darts[k]
        g = rng.randrange(N)
        if g == old:
            continue
        if any(dd[0] == i and dd[1] == j and dd[2] == g for dd in darts):
            continue
        darts[k][2] = g
        dout2, din2 = _tables(b, darts, invs)
        v = _unreached(b, N, T, dout2, din2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            dout, din = dout2, din2
        else:
            darts[k][2] = old
    if cur == 0:
        return darts
    return None


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N with base size b until a lift of diameter <= D is found."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        M = _sample_base(b, d, rng)
        if M is None:
            continue
        darts = _anneal(b, N, T, invs, d, D, M, rng, ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift_edges(b, N, T, darts):
    """Expand a solved dart set into (n, edges)."""
    BN = b * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, BN + j * N + T[x][g]))
    return 2 * BN, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
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
    budget = 0.5
    tried = set()

    while time.monotonic() < deadline:
        all_cands = []
        for b in range(1, MAX_BASE + 1):
            lo = best_n // (2 * b) + 1
            for N in range(max(lo, d + 1), lo + WINDOW):
                if best_n < 2 * b * N <= moore:
                    all_cands.append((2 * b * N, b, N))
        if not all_cands:
            break
        cands = sorted(c for c in all_cands if (c[1], c[2]) not in tried)
        if not cands:
            budget *= 2
            tried = set()
            continue
        for _, b, N in cands:
            if time.monotonic() >= deadline:
                break
            att = min(deadline, time.monotonic() + budget)
            res = _attempt(b, N, d, D, rng, att)
            tried.add((b, N))
            if res is not None:
                T, darts = res
                n, e = _lift_edges(b, N, T, darts)
                consider(n, e)
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
