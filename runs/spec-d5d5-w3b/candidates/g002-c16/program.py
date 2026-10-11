import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: projective planes (D = 3) and generalized quadrangles (D = 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base cyclic voltage lifts evaluated with big-integer bitsets.
#
# Base graph: k A-classes and k B-classes, each class has d darts (one per
# layer L). Layer L is a permutation P[L] sending A_i to B_{P[L][i]} with
# voltage V[L][i]. The lift on Z_N has vertices A_i,x and B_j,y with
# A_i,x ~ B_j,(x+s). Translation by Z_N is an automorphism, so the diameter
# check only needs BFS from one representative per class.
#
# Each BFS layer is computed with N-bit integers: a rotation of a bitset is a
# shift plus a wrap-around. Simulated annealing minimises the number of
# unreached (source, vertex) pairs.
# ----------------------------------------------------------------------------

SLICE = 4.0  # seconds per (k, N) attempt


def _cost(k, N, D, darts, full):
    """Number of unreached (source, vertex) pairs over the 2k class sources. Zero means valid.

    Duplicate darts (same class pair and voltage) are penalised, since they would
    produce duplicate edges.
    """
    nc = 2 * k
    dup = len(darts) - len(set(darts))
    total = dup * 4 * N * nc
    for src in range(nc):
        seen = [0] * nc
        front = [0] * nc
        seen[src] = 1
        front[src] = 1
        for _ in range(D):
            new = [0] * nc
            for i, j, s in darts:
                fi = front[i]
                if fi:
                    new[k + j] |= ((fi << s) | (fi >> (N - s))) & full
                fb = front[k + j]
                if fb:
                    t = (N - s) % N
                    new[i] |= ((fb << t) | (fb >> (N - t))) & full
            alive = 0
            for c in range(nc):
                nw = new[c] & ~seen[c]
                seen[c] |= nw
                front[c] = nw
                alive |= nw
            if not alive:
                break
        total += nc * N - sum(x.bit_count() for x in seen)
    return total


def _search(d, D, k, N, rng, deadline):
    """Anneal voltages and layer permutations for a k-base lift over Z_N. Returns darts or None."""
    full = (1 << N) - 1
    P = [rng.sample(range(k), k) for _ in range(d)]
    V = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]

    def darts_now():
        return [(i, P[L][i], V[L][i]) for L in range(d) for i in range(k)]

    while time.monotonic() < deadline:
        for L in range(d):
            P[L] = rng.sample(range(k), k)
            V[L] = [rng.randrange(N) for _ in range(k)]
        cur = _cost(k, N, D, darts_now(), full)
        T0, T1, iters = 2.0, 0.15, 2000
        for it in range(iters):
            if cur == 0:
                break
            if (it & 31) == 0 and time.monotonic() > deadline:
                break
            T = T0 * (T1 / T0) ** (it / iters)
            L = rng.randrange(d)
            oldP, oldV = P[L][:], V[L][:]
            r = rng.random()
            if r < 0.4 or k == 1:
                i = rng.randrange(k)
                V[L][i] = rng.randrange(N)
            elif r < 0.6:
                i = rng.randrange(k)
                V[L][i] = (V[L][i] + rng.choice((-2, -1, 1, 2))) % N
            else:
                a, b = rng.sample(range(k), 2)
                P[L][a], P[L][b] = P[L][b], P[L][a]
            c2 = _cost(k, N, D, darts_now(), full)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
            else:
                P[L] = oldP
                V[L] = oldV
        if cur == 0:
            return darts_now()
    return None


def _lift_edges(k, N, darts):
    """Expand base darts into the Z_N lift: vertices i*N + x (A side) and (k+j)*N + y (B side)."""
    E = []
    for i, j, s in darts:
        for x in range(N):
            E.append((i * N + x, (k + j) * N + (x + s) % N))
    return 2 * k * N, E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: bipartite, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and best[0] < moore:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: multi-base cyclic lifts above the current best order.
    cur_N = {}
    while best[0] < moore and time.monotonic() < deadline:
        k = rng.choice((1, 2, 2, 3, 3, 4))
        lo = best[0] // (2 * k) + 1
        N = max(cur_N.get(k, lo), lo)
        if N > moore // (2 * k):
            cur_N[k] = lo
            if lo > moore // (2 * k):
                continue
            N = lo
        slice_end = min(deadline, time.monotonic() + SLICE)
        darts = _search(d, D, k, N, rng, slice_end)
        if darts is not None:
            n, e = _lift_edges(k, N, darts)
            consider(n, e)
            cur_N[k] = N + rng.randint(1, 3)
        else:
            cur_N[k] = max(lo, N - 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
