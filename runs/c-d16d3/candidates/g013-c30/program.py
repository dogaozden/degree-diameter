import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction A: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1. Add a vertex for chosen points (joined to their q+1 lines) and
# for chosen lines (joined to their q+1 points), keeping every old vertex within
# the degree bound d.
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


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so every target is hit by <= s of them."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
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


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Construction B (new, bold): group Haar graphs from difference covers.
#
# Let G be a finite group of order M and S a subset of size k <= d. Put
# X = G, Y = G (two copies) and join x in X to y in Y iff x^{-1} y is in S.
# This graph is k-regular and bipartite with 2M vertices.
#   * Two X-vertices x, x' share a neighbour iff x^{-1} x' is in S S^{-1}.
#   * Any X-vertex and Y-vertex are at distance <= 3 when S S^{-1} = G, because
#     then the cross pair is joined by a path of length 3 (x, xa, xab^{-1}, y).
# So if S S^{-1} = G, the diameter is 3. The order bound is k(k-1)+1 (the
# difference-cover bound), so with k = d the order can reach 2(d^2-d+1)
# in principle. The search finds such S by simulated annealing on the number of
# covered differences, for groups of decreasing order M.
# ----------------------------------------------------------------------------

def _groups_for(M, rng):
    """Return a few groups (order, mul, inv) of order M: cyclic plus some semidirect products."""
    out = [lib.cyclic_group(M)]
    opts = []
    for k2 in range(2, M // 2 + 1):
        if M % k2:
            continue
        m = M // k2
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not rs:
            continue
        for r in rng.sample(rs, min(len(rs), 2)):
            opts.append((m, k2, r))
    rng.shuffle(opts)
    for m, k2, r in opts[:2]:
        try:
            out.append(lib.semidirect_group(m, k2, r))
        except ValueError:
            pass
    return out


def _cover_search(M, k, T, I, rng, budget):
    """Simulated annealing for a k-subset S with S S^{-1} = G. Returns S (list) or None."""
    t_end = time.monotonic() + budget
    cnt = [0] * M
    cov = [0]
    S = []

    def inc(g):
        if cnt[g] == 0:
            cov[0] += 1
        cnt[g] += 1

    def dec(g):
        cnt[g] -= 1
        if cnt[g] == 0:
            cov[0] -= 1

    def add(x):
        for b in S:
            inc(T[x][I[b]])
            inc(T[b][I[x]])
        inc(T[x][I[x]])
        S.append(x)

    def remove_at(i):
        x = S[i]
        S[i] = S[-1]
        S.pop()
        for b in S:
            dec(T[x][I[b]])
            dec(T[b][I[x]])
        dec(T[x][I[x]])

    for x in rng.sample(range(M), k):
        add(x)

    temp = 0.5
    it = 0
    while cov[0] < M:
        it += 1
        if it % 128 == 0 and time.monotonic() > t_end:
            return None
        i = rng.randrange(k)
        y = rng.randrange(M)
        if y in S:
            continue
        x = S[i]
        before = cov[0]
        remove_at(i)
        add(y)
        delta = cov[0] - before
        if delta < 0 and rng.random() >= math.exp(delta / temp):
            remove_at(S.index(y))
            add(x)
    return list(S)


def _haar_from(M, S, T):
    """Bipartite graph X = G, Y = G, x ~ y iff x*s = y for some s in S (order 2M)."""
    E = [(x, M + T[x][s]) for x in range(M) for s in S]
    return 2 * M, E


def _group_search(d, floor_n, deadline, rng, consider):
    """Descend through orders M of groups, searching S with S S^{-1} = G, |S| = min(d, M)."""
    Mtop = d * (d - 1) + 1
    Mlow = max(2, floor_n // 2 + 1)
    if Mtop < Mlow:
        return
    M = Mtop
    while M >= Mlow and time.monotonic() < deadline:
        remaining = M - Mlow + 1
        per_M = (deadline - time.monotonic()) / remaining
        k = min(d, M)
        groups = _groups_for(M, rng)
        slot = per_M / max(1, len(groups))
        for order, mul, inv in groups:
            if time.monotonic() > deadline:
                return
            T = [[mul(x, y) for y in range(M)] for x in range(M)]
            I = [inv(x) for x in range(M)]
            S = _cover_search(M, k, T, I, rng, slot)
            if S is not None:
                n, e = _haar_from(M, S, T)
                consider(n, e)
                return
        M -= 1


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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
# Driver. Every candidate passes lib.is_valid before it can replace the best.
# Fallback: K_{d,d}, which has diameter 2 and is valid for all D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

        if time.monotonic() < deadline:
            _group_search(d, best_n, deadline, rng, consider)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
