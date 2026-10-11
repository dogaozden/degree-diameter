import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
#
# Start from the point-line incidence graph of PG(2, q): 2m vertices with
# m = q^2+q+1, every vertex of degree q+1. Let s = d - q - 1 be the spare degree.
#
#   * Choose SA, a set of points with at most s of them on any line. For each
#     P in SA add a new vertex joined to the q+1 lines through P. This loads
#     each old line by at most s.
#   * Choose SB, a set of lines with at most s of them through any point. For
#     each J in SB add a new vertex joined to the q+1 points on J. This loads
#     each old point by at most s.
#
# SA and SB are chosen independently. The order is 2m + |SA| + |SB|, and the
# upper bound is 2m + 2*floor(s*m/(q+1)). Diameter 3 is preserved: two new
# A-vertices share the line PP', two new B-vertices share a point, and a new
# A-vertex to a new B-vertex has the path A_P - L - Q - B_J with L through P
# and Q = L cap J.
#
# The sets SA and SB are found by a randomized local search (add, swap, and an
# occasional drop), which replaces the parent's one-shot greedy.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, point_lines, line_points) for PG(2, q); lines use indices 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, point_lines, line_points


def _max_arc(m, s, inc, mem, rng, deadline):
    """Local search for a large set S of indices in 0..m-1 with every cell loaded <= s.

    Adding x increments the cells inc[x]. The members of cell c are mem[c].
    Returns the largest feasible set found before the deadline.
    """
    inS = [False] * m
    cl = [0] * m
    S = []
    best = []

    def add(x):
        inS[x] = True
        S.append(x)
        for c in inc[x]:
            cl[c] += 1

    def remove(x):
        inS[x] = False
        S.remove(x)
        for c in inc[x]:
            cl[c] -= 1

    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        full = [c for c in inc[P] if cl[c] >= s]
        f = len(full)
        if f == 0:
            add(P)
        elif f == 1:
            # Plateau move: swap out one member of the full cell.
            cands = [x for x in mem[full[0]] if inS[x]]
            remove(rng.choice(cands))
            add(P)
        elif f == 2 and rng.random() < 0.03:
            # Occasional downhill move, to escape plateaus.
            for c in full:
                remove(rng.choice([x for x in mem[c] if inS[x]]))
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


def _assemble(m, point_lines, line_points, SA, SB):
    """Old incidence graph plus one new A-vertex per SA point and one new B-vertex per SB line."""
    E = []
    for u in range(m):
        for j in point_lines[u]:
            E.append((u, m + j))
    nA = len(SA)
    n = 2 * m + nA + len(SB)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, J in enumerate(SB):
        b = 2 * m + nA + t
        for Q in line_points[J]:
            E.append((Q, b))
    return n, E


def _arc_for_q(q, s, deadline, rng):
    """Build the arc-extended graph for PG(2, q) with spare degree s."""
    m, point_lines, line_points = _pg_data(q)
    if s <= 0:
        return _assemble(m, point_lines, line_points, [], [])
    now = time.monotonic()
    mid = now + (deadline - now) * 0.5
    SA = _max_arc(m, s, point_lines, line_points, rng, mid)
    SB = _max_arc(m, s, line_points, point_lines, rng, deadline)
    return _assemble(m, point_lines, line_points, SA, SB)


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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Order the prime powers q (q + 1 <= d) by the upper bound on the order.
        qs = []
        for q in range(2, min(d - 1, 23) + 1):
            if not lib.is_prime_power(q):
                continue
            s = d - q - 1
            m = q * q + q + 1
            ub = 2 * m + (2 * (s * m // (q + 1)) if s > 0 else 0)
            qs.append((ub, q, s))
        qs.sort(reverse=True)
        for ub, q, s in qs:
            if ub <= best_n:
                continue
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.2:
                break
            qdl = now + remaining * 0.7
            n_c, e_c = _arc_for_q(q, s, qdl, rng)
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 4:
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
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
