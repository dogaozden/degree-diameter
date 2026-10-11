import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

WINDOW = 4            # bi-Cayley orders tried just above the current lower bound
MAX_GROUPS = 6        # groups tried per bi-Cayley order
TABU_STEPS = 100      # tabu steps per (order, group) attempt
TABU_SAMPLE = 100     # sampled single-swap moves examined per tabu step
TABU_TENURE = 7       # base tabu tenure (random extra 0..2 added)
ANNEAL_ITERS = 1500   # annealing steps for multi-base lifts
_BIG = 10 ** 9
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# D = 3 and D = 4 baselines: projective planes, arc extensions, quadrangles.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
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


def _local_improve(m, s, point_lines, line_points, S, rng, deadline, iters):
    """Plateau-walking 1-swap local search growing a feasible load-bounded set S."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m

    def add(P):
        inS[P] = True
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def rem(P):
        inS[P] = False
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fits(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    cur = list(S)
    for P in cur:
        add(P)
    best = list(cur)
    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            add(P)
            cur.append(P)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        R = cur[idx]
        rem(R)
        if fits(P):
            add(P)
            cur[idx] = P
        else:
            add(R)
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
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _local_improve(m, s, point_lines, line_points, g, rng, deadline, 3000)
            cands.append(g)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Group tables, vectorised.
#
# For Z_m x|_r Z_k (element a*k+b, multiplication (a,b)(c,d) = (a + r^b c, b + d)),
# T[x, g] = x*g as a numpy array. Built with broadcasting instead of Python loops.
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


def _group_tables(m, k, r):
    """Cached (order, T) with T an int64 array, T[x, g] = x*g."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    idx = np.arange(G, dtype=np.int64)
    A = idx // k
    B = idx % k
    T = ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    val = (G, T)
    if len(_TABLE_CACHE) >= 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


# ----------------------------------------------------------------------------
# NEW: matrix-power ball evaluator.
#
# Instead of a BFS per source, build the dense 0/1 adjacency (with identity)
# and propagate only the rows of the representative vertices:
#     P_0 = M[reps],  P_{t+1} = min(P_t @ M, 1).
# After D-1 products each row of P is the radius-D ball of a representative.
# The return value counts (representative, vertex) pairs at distance > D.
# Zero means every representative reaches everything within D, which for a
# vertex-transitive-per-side lift is the full diameter check.
# ----------------------------------------------------------------------------

def _dense_uncovered(n, a_idx, b_idx, reps, D):
    M = np.zeros((n, n), dtype=np.float32)
    M[a_idx, b_idx] = 1.0
    M[b_idx, a_idx] = 1.0
    np.fill_diagonal(M, 1.0)
    P = M[reps]
    for _ in range(D - 1):
        P = np.minimum(P @ M, 1.0)
    return len(reps) * n - int(np.count_nonzero(P))


def _bicayley_uncovered(N, T, S, D):
    """Uncovered pairs for the bi-Cayley graph A_x -- B_{x s}, s in S (A_0 and B_0 representatives)."""
    cols = T[:, S]
    a = np.broadcast_to(np.arange(N, dtype=np.int64)[:, None], cols.shape).ravel()
    b = (N + cols).ravel()
    return _dense_uncovered(2 * N, a, b, np.array([0, N], dtype=np.int64), D)


def _lift_uncovered(k, G, T, darts, D):
    """Uncovered pairs for a multi-base lift; dart (i, j, s) joins A_{i,g} to B_{j, g*s}."""
    ar = np.arange(G, dtype=np.int64)
    a = np.concatenate([i * G + ar for i, _, _ in darts])
    b = np.concatenate([(k + j) * G + T[:, s] for _, j, s in darts])
    reps = np.array([i * G for i in range(k)] + [(k + j) * G for j in range(k)], dtype=np.int64)
    return _dense_uncovered(2 * k * G, a, b, reps, D)


# ----------------------------------------------------------------------------
# NEW: sampled tabu search over bi-Cayley connection sets.
#
# The identity is fixed in S (WLOG). Each step samples single-position swaps,
# takes the best non-tabu one (aspiration allows tabu moves that beat the best
# value seen), and forbids restoring the old element at that position for a
# short tenure.
# ----------------------------------------------------------------------------

def _tabu_connection_set(N, T, d, D, rng, deadline, steps):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _bicayley_uncovered(N, T, S, D)
    best_val = cur
    tabu = {}
    for step in range(steps):
        if cur == 0 or time.monotonic() > deadline:
            break
        in_S = set(S)
        best_move = None
        for _ in range(TABU_SAMPLE):
            pos = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in in_S:
                continue
            S2 = S[:]
            S2[pos] = c
            v = _bicayley_uncovered(N, T, S2, D)
            if tabu.get((pos, c), -1) > step and v >= best_val:
                continue
            if best_move is None or v < best_move[0]:
                best_move = (v, pos, c)
        if best_move is None:
            continue
        v, pos, c = best_move
        tabu[(pos, S[pos])] = step + TABU_TENURE + rng.randrange(3)
        S[pos] = c
        cur = v
        if cur < best_val:
            best_val = cur
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products, annealed.
# Each of the d layers is a perfect matching between k A-base and k B-base
# vertices, with one voltage per dart.
# ----------------------------------------------------------------------------

def _lift_cost(k, G, T, darts, D):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    return _lift_uncovered(k, G, T, darts, D)


def _lift_edges(k, G, T, darts):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + int(T[g, s])))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, T, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _lift_cost(k, G, T, darts, D)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    temp = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(T_end, temp * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            c2 = _lift_cost(k, G, T, darts, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[idx][2] = old_s
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _lift_cost(k, G, T, darts, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, T, darts)
    return None


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

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound 2d for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] < moore:
            for n_c, e_c in _arc_extensions(d, start + 0.3 * budget,
                                            random.Random(seed * 7919 + d)):
                consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: aim strictly above the current best order.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break

        if d >= 2 and rng.random() < 0.75:
            N = lo + rng.randrange(WINDOW)
            if N > moore // 2:
                N = lo
            groups = _groups(N)
            rng.shuffle(groups)
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, T = _group_tables(m, k2, r)
                S = _tabu_connection_set(N, T, d, D, rng, deadline, TABU_STEPS)
                if S is not None:
                    cols = T[:, S].tolist()
                    edges = [(x, N + c) for x in range(N) for c in cols[x]]
                    consider(2 * N, edges)
                    if best[0] >= 2 * N:
                        break
        else:
            k = rng.choice((2, 3))
            lo_g = n_best // (2 * k) + 1
            if 2 * k * lo_g > moore:
                continue
            G = lo_g + rng.randrange(max(2, lo_g // 10))
            cands = _groups(G)
            if not cands:
                continue
            m, k2, r = rng.choice(cands)
            G2, T = _group_tables(m, k2, r)
            res = _anneal_lift(d, D, k, G2, T, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
