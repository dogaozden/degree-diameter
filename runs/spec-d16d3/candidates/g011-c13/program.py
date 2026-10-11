import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# PG(2, q) helpers. Points and lines share the index set 0..m-1 (same vectors).
# Old line L is the vertex m+L in the incidence graph.
# ----------------------------------------------------------------------------

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


def _bits(x):
    """Indices of the set bits of the integer bitmask x."""
    out = []
    while x:
        low = x & -x
        out.append(low.bit_length() - 1)
        x ^= low
    return out


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
    """Randomized greedy point set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


# ----------------------------------------------------------------------------
# Cover packing (diameter 3).
#
# An A-vertex x joined to a set T of lines, and a B-vertex y joined to a set U
# of points. Requirements for diameter 3 (old vertices stay within 3 already):
#   - T covers every point (x reaches each point within 2);
#   - two A-vertices have intersecting T's (distance 2);
#   - U covers every line, and B-covers pairwise intersect (symmetric);
#   - A and B are at distance <= 3 automatically (T covers, U nonempty).
# Each line may serve at most s = d-q-1 A-covers (its degree is q+1 plus that),
# and each point at most s B-covers. The A side and B side are independent.
# So we pack as many such covers as possible on each side.
# ----------------------------------------------------------------------------

def _grow_cover(m, cover_of, load, cap, dmax, covers, rng):
    """Greedy randomized cover that hits every existing cover and covers the universe.

    cover_of[c] is a bitmask over the universe; candidates are 0..m-1.
    Returns a candidate bitmask with at most dmax candidates, or None.
    """
    uncovered = (1 << m) - 1
    unhit = list(covers)
    chosen = 0
    size = 0
    while uncovered or unhit:
        if size >= dmax:
            return None
        h = [0] * m
        for T in unhit:
            for c in _bits(T):
                h[c] += 1
        best_key = None
        best_c = -1
        for c in range(m):
            if load[c] >= cap or (chosen >> c) & 1:
                continue
            sc = (cover_of[c] & uncovered).bit_count() + h[c]
            if sc <= 0:
                continue
            key = sc + rng.random() * 0.9
            if best_key is None or key > best_key:
                best_key = key
                best_c = c
        if best_c < 0:
            return None
        chosen |= 1 << best_c
        size += 1
        uncovered &= ~cover_of[best_c]
        unhit = [T for T in unhit if not (T >> best_c) & 1]
    return chosen


def _pack_side(m, cover_of, cap, dmax, rng, deadline, init):
    """Pack intersecting covers greedily until the deadline. init are candidate masks kept first."""
    load = [0] * m
    covers = []
    for T in init:
        covers.append(T)
        for c in _bits(T):
            load[c] += 1
    if cap <= 0:
        return covers
    fails = 0
    while time.monotonic() < deadline and fails < 3000:
        T = _grow_cover(m, cover_of, load, cap, dmax, covers, rng)
        if T is None:
            fails += 1
            continue
        fails = 0
        covers.append(T)
        for c in _bits(T):
            load[c] += 1
    return covers


def _best_side(m, cover_of, cap, dmax, rng, deadline, init):
    """Run arc-seeded packing and from-scratch packing, keep the larger family."""
    now = time.monotonic()
    mid = now + 0.5 * max(0.0, deadline - now)
    a = _pack_side(m, cover_of, cap, dmax, rng, mid, init)
    b = _pack_side(m, cover_of, cap, dmax, rng, deadline, [])
    return a if len(a) >= len(b) else b


def _assemble(m, edges, A, B):
    """Old PG(2,q) incidence plus an A-vertex per line-cover and a B-vertex per point-cover."""
    nA, nB = len(A), len(B)
    n = 2 * m + nA + nB
    E = list(edges)
    for t, T in enumerate(A):
        x = 2 * m + t
        for L in _bits(T):
            E.append((x, m + L))
    for t, U in enumerate(B):
        y = 2 * m + nA + t
        for P in _bits(U):
            E.append((P, y))
    return n, E


def _d3_for_q(d, q, deadline, rng):
    """Build the packed diameter-3 graph for one prime power q (s = d-q-1 spare degree)."""
    s = d - q - 1
    m, edges, point_lines, line_points, index, pts = _pg_data(q)
    if s == 0:
        return 2 * m, list(edges)
    cands = [_greedy_arc(m, s, point_lines, line_points, rng, 20, deadline)]
    if s >= 2:
        cs = _conic_set(q, index, lib.GF(q))
        if _loads_ok(cs, s, m, point_lines, line_points):
            cands.append(cs)
    S = max(cands, key=len)
    # Pencil of P (A side) = lines through P; dual pencil (B side) = points on line P.
    arc_A = [sum(1 << L for L in point_lines[P]) for P in S]
    arc_B = [sum(1 << Q for Q in line_points[P]) for P in S]
    # A side: universe = points, candidates = lines. B side: universe = lines, candidates = points.
    cover_A = [sum(1 << Q for Q in line_points[L]) for L in range(m)]
    cover_B = [sum(1 << L for L in point_lines[P]) for P in range(m)]
    now = time.monotonic()
    mid = now + 0.5 * max(0.0, deadline - now)
    A = _best_side(m, cover_A, s, d, rng, mid, arc_A)
    B = _best_side(m, cover_B, s, d, rng, deadline, arc_B)
    return _assemble(m, edges, A, B)


def _d3_search(d, deadline, rng, floor_n):
    """Best diameter-3 graph over prime powers q <= d-1, or None if none beats floor_n."""
    jobs = []
    for q in range(2, min(d, 24)):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        m = q * q + q + 1
        ub = 2 * m + (2 * (m * s) // (q + 1) if s >= 1 else 0)
        if ub > floor_n:
            jobs.append((ub, q))
    jobs.sort(reverse=True)
    best, best_n = None, floor_n
    for ub, q in jobs:
        now = time.monotonic()
        if now >= deadline or ub <= best_n:
            continue
        qdead = now + 0.7 * (deadline - now)
        res = _d3_for_q(d, q, qdead, rng)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, 3):
            best, best_n = res, res[0]
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (D = 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.72 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    # Diameter-3 packed constructions are valid for every D >= 3.
    if D >= 3:
        d3_deadline = deadline if D == 3 else start + 0.25 * time_limit
        res = _d3_search(d, d3_deadline, rng, best_n)
        if res is not None and res[0] > best_n:
            best, best_n = res, res[0]

    if D == 3:
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return lib.haar_graph(d, range(d))

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best_n and lib.is_valid(gq[0], gq[1], d, D):
            best, best_n = gq, gq[0]

    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best, best_n = res, res[0]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
