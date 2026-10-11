import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3: projective planes and arc extensions (kept from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        if not cands:
            continue
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# D >= 4 baseline: generalized quadrangle W(q), diameter 4.
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW FAMILY: multi-block cyclic voltage lifts evaluated with bitsets.
#
# The graph has k A-blocks and k B-blocks, each block a copy of Z_N.
# A dart (i, j, a) joins A-vertex (i, x) to B-vertex (j, x + a) for all x.
# Layer L contributes one dart per block, so every vertex has degree d
# provided all darts are distinct. Z_N translation is an automorphism of
# every block, so eccentricities need only be checked from one vertex per block.
#
# Reachability is computed with N-bit integers: rotating a bitmask is a
# translation of its indices. This makes the diameter test very fast, so
# simulated annealing can run thousands of evaluations per second.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 3000
_BIG = 10 ** 6


def _rot(x, a, N, full):
    """Translate the bitmask x by a (bit i moves to i + a mod N)."""
    if a == 0:
        return x
    return ((x << a) | (x >> (N - a))) & full


def _unreached(k, N, darts, D):
    """Total (source, vertex) pairs not within distance D, over one source per block."""
    full = (1 << N) - 1
    total_vertices = 2 * k * N
    total = 0
    for s in range(2 * k):
        X = [0] * k
        Y = [0] * k
        if s < k:
            X[s] = 1
        else:
            Y[s - k] = 1
        for _ in range(D):
            nX = list(X)
            nY = list(Y)
            for i, j, a in darts:
                # A-vertex x is adjacent to B-vertex x + a, so A gains rot(Y_j, -a).
                nX[i] |= _rot(Y[j], (N - a) % N, N, full)
                # B-vertex y is adjacent to A-vertex y - a, so B gains rot(X_i, a).
                nY[j] |= _rot(X[i], a, N, full)
            X, Y = nX, nY
        reached = sum(x.bit_count() for x in X) + sum(y.bit_count() for y in Y)
        total += total_vertices - reached
    return total


def _cost(k, N, darts, D):
    """Zero means the lift is valid; duplicate darts give a large penalty."""
    if len(set(darts)) < len(darts):
        return _BIG
    return _unreached(k, N, darts, D)


def _anneal_lift(k, N, d, D, rng, deadline, iters):
    """Anneal voltages and layer permutations for a k-block lift over Z_N.

    WLOG layer 0 is the identity permutation with zero voltages, since
    relabelling blocks and shifting coordinates removes those degrees of freedom.
    """
    if d < 2 or N < d:
        return None
    perms = [list(range(k))] + [rng.sample(range(k), k) for _ in range(d - 1)]
    volt = [[0] * k] + [[rng.randrange(N) for _ in range(k)] for _ in range(d - 1)]

    def darts():
        return [(i, perms[L][i], volt[L][i]) for L in range(d) for i in range(k)]

    cur = _cost(k, N, darts(), D)
    T0, T1 = 3.0, 0.2
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        if k == 1 or rng.random() < 0.8:
            L = rng.randrange(1, d)
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(N)
            if new == old:
                continue
            volt[L][i] = new
            c2 = _cost(k, N, darts(), D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                volt[L][i] = old
        else:
            L = rng.randrange(1, d)
            i, i2 = rng.sample(range(k), 2)
            row = perms[L]
            row[i], row[i2] = row[i2], row[i]
            c2 = _cost(k, N, darts(), D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                row[i], row[i2] = row[i2], row[i]
    return darts() if cur == 0 else None


def _lift_edges(k, N, darts):
    """Expand darts into the explicit simple graph. A-block i is ids i*N.., B-block j is (k+j)*N.."""
    E = set()
    for i, j, a in darts:
        for x in range(N):
            E.add((i * N + x, (k + j) * N + (x + a) % N))
    return 2 * k * N, sorted(E)


def _search_lifts(d, D, best, moore, rng, deadline):
    """Repeatedly anneal block lifts aimed just above the current best order."""
    while time.monotonic() < deadline and best[0] < moore:
        n_best = best[0]
        ks = [k for k in (1, 2, 3, 4) if 2 * k * (n_best // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        N = n_best // (2 * k) + 1
        if rng.random() < 0.5:
            N += rng.randrange(0, 4)
        if 2 * k * N > moore:
            N = n_best // (2 * k) + 1
        darts = _anneal_lift(k, N, d, D, rng, deadline, ANNEAL_ITERS)
        if darts is not None:
            n, e = _lift_edges(k, N, darts)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] < moore:
            for n_c, e_c in _arc_extensions(d, start + 0.4 * budget,
                                            random.Random(seed * 7919 + d)):
                consider(n_c, e_c)
    else:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        if best[0] < moore:
            best = _search_lifts(d, D, best, moore, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
