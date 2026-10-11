import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane based constructions (diameter 3 and 4).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# Baseline ("arc" extension): add one A-vertex per point of a set SA, joined to
# the q+1 lines through it, and one B-vertex per line of SB, joined to its
# q+1 points. Each line may carry at most s A-vertices, each point at most s
# B-vertices.
#
# Cover extension (new in this version): an A-vertex may be joined to ANY set
# of at most d lines that covers every point of PG(2, q). A family of such
# covers is valid when
#   (1) any two A-covers share a line (A-A distance 2),
#   (2) every line lies in at most s covers (degree bound),
# and the dual condition holds for B-vertices (point covers of the lines).
# The distance checks work out for every pair of vertex types:
#   A to point: covered, so distance 2.   A to line: x-L-Q-M, distance 3.
#   A to B: x-L-Q-B with Q on both L and the B-set, distance 3.
#   B to line: covered dually, so distance 2.   B to point: distance 3.
# Stars (all lines through one point) are the special case used by the arc
# baseline, so the cover search can only add to it.
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
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Cover-family search for one side.
#
# Resources are the m lines (A side) or m points (B side). res_t[r] lists the
# targets that resource r covers. A cover is a list of at most K resources
# that together cover all m targets. The family must be pairwise intersecting
# and each resource lies in at most s covers.
# ----------------------------------------------------------------------------

def _cover_side(m, s, K, res_t, deadline, rng):
    """Local search for a large family of covers. Returns a list of covers (lists of resources)."""

    def rebuild(cs):
        load = [0] * m
        member = [[] for _ in range(m)]
        for j, c in enumerate(cs):
            for r in c:
                load[r] += 1
                member[r].append(j)
        return load, member

    def try_build(cs, load, member):
        """Greedy cover that hits every existing cover and covers every target, or None."""
        covered = [0] * m
        uncov = m
        unhit = set(range(len(cs)))
        chosen = []
        used = [False] * m
        while uncov or unhit:
            if len(chosen) >= K:
                return None
            best_r, best_sc = -1, -1.0
            for r in range(m):
                if used[r] or load[r] >= s:
                    continue
                g = 0
                for t in res_t[r]:
                    if covered[t] == 0:
                        g += 1
                h = 0
                for j in member[r]:
                    if j in unhit:
                        h += 1
                if g == 0 and h == 0:
                    continue
                sc = g + 2.0 * h + 0.9 * rng.random()
                if sc > best_sc:
                    best_sc, best_r = sc, r
            if best_r < 0:
                return None
            r = best_r
            used[r] = True
            chosen.append(r)
            for t in res_t[r]:
                if covered[t] == 0:
                    uncov -= 1
                covered[t] += 1
            for j in member[r]:
                unhit.discard(j)
        return chosen

    cur = []
    best = []
    while time.monotonic() < deadline:
        load, member = rebuild(cur)
        c = try_build(cur, load, member)
        if c is not None:
            cur.append(c)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            break
        # Perturbation: drop one cover and try to rebuild up to two covers.
        saved = list(cur)
        cur.pop(rng.randrange(len(cur)))
        for _ in range(2):
            load, member = rebuild(cur)
            c = try_build(cur, load, member)
            if c is None:
                break
            cur.append(c)
        if len(cur) < len(saved):
            cur = saved
        if len(cur) > len(best):
            best = list(cur)
    return best


def _cover_graph(m, edges, covA, covB):
    """Build the graph: PG incidence plus A-vertices (joined to lines) and B-vertices (joined to points)."""
    na = len(covA)
    n = 2 * m + na + len(covB)
    E = list(edges)
    for t, c in enumerate(covA):
        x = 2 * m + t
        for L in c:
            E.append((x, m + L))
    for t, c in enumerate(covB):
        b = 2 * m + na + t
        for P in c:
            E.append((P, b))
    return n, E


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
# Simulated annealing over bi-Cayley voltage lifts (fallback for D >= 4).
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
    deadline = start + 0.75 * time_limit
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
        # Baseline: arc-extended projective plane graphs (fast, always valid for D >= 3).
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

        # Cover-family search on the largest prime powers q with q + 1 <= d and spare degree.
        qs = sorted([q for q in range(2, d)
                     if lib.is_prime_power(q) and d - q - 1 >= 1], reverse=True)[:2]
        if qs and time.monotonic() < deadline:
            t0 = time.monotonic()
            span = deadline - t0
            cum = 0.0
            for idx, q in enumerate(qs):
                share = (0.7 if idx == 0 else 0.3) if len(qs) > 1 else 1.0
                cum += share
                sub_dl = t0 + cum * span
                now = time.monotonic()
                if now >= sub_dl:
                    continue
                m, edges, point_lines, line_points, _index, _pts = _pg_data(q)
                s = d - q - 1
                mid = now + (sub_dl - now) / 2.0
                covA = _cover_side(m, s, d, line_points, mid, rng)
                covB = _cover_side(m, s, d, point_lines, sub_dl, rng)
                if covA or covB:
                    n_c, e_c = _cover_graph(m, edges, covA, covB)
                    consider(n_c, e_c)

    if D >= 4:
        if time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        # Annealed group voltage lifts for the remaining time.
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
