import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane helpers (shared by the arc base and the growth search).
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


def _arc_base(d, rng, deadline):
    """Best arc-extended PG(2,q) graph for degree d.

    Vertex layout: points 0..m-1, lines m..2m-1, new A-vertices 2m..2m+k-1 (side 0),
    new B-vertices 2m+k..2m+2k-1 (side 1). Returns (n, edges, nold, side) or None.
    nold = 2m counts the untouched projective-plane vertices.
    """
    best = None
    for q in range(2, min(d - 2, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1 or time.monotonic() > deadline:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        k = len(S)
        n = 2 * m + 2 * k
        if best is not None and n <= best[0]:
            continue
        E = list(edges)
        for t, P in enumerate(S):
            for L in point_lines[P]:
                E.append((2 * m + t, m + L))
        for t, j in enumerate(S):
            for Q in line_points[j]:
                E.append((Q, 2 * m + k + t))
        side = [0] * m + [1] * m + [0] * k + [1] * k
        best = (n, E, 2 * m, side)
    return best


# ----------------------------------------------------------------------------
# Growth search: keep the old PG(2,q) vertices fixed, and anneal the variable
# attachments (A-lines, B-points, A-B, plus the base A/B vertices) so that one
# more A/B pair fits while the diameter stays 3.
# ----------------------------------------------------------------------------

def _bad3(adj):
    """Number of unordered vertex pairs at distance > 3 (unreachable pairs count)."""
    n = len(adj)
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _grow_arcs(base, d, deadline, rng):
    """Try to add A/B pairs one at a time by annealing attachments. Returns (n, edges) of the best valid graph."""
    n0, E, nold, side0 = base
    side = list(side0)
    adj = [set() for _ in range(n0)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    var = []
    pos = {}
    for u, v in E:
        if u >= nold or v >= nold:
            key = (u, v) if u < v else (v, u)
            pos[key] = len(var)
            var.append(key)

    def allowed(u, v):
        return (u != v and side[u] != side[v] and (u >= nold or v >= nold)
                and v not in adj[u] and len(adj[u]) < d and len(adj[v]) < d)

    def link(u, v):
        adj[u].add(v)
        adj[v].add(u)
        key = (u, v) if u < v else (v, u)
        pos[key] = len(var)
        var.append(key)

    def unlink(u, v):
        adj[u].discard(v)
        adj[v].discard(u)
        key = (u, v) if u < v else (v, u)
        i = pos.pop(key)
        last = var.pop()
        if i < len(var):
            var[i] = last
            pos[last] = i

    def pick_pair():
        n = len(adj)
        for _ in range(100):
            if n > nold and rng.random() < 0.7:
                u = rng.randrange(nold, n)
            else:
                u = rng.randrange(n)
            w = rng.randrange(n)
            if allowed(u, w):
                return u, w
        return None

    def pick_partner(x):
        n = len(adj)
        for _ in range(100):
            y = rng.randrange(n)
            if allowed(x, y):
                return y
        return None

    def anneal(end):
        """Anneal until the graph has no bad pairs (True) or time runs out (False)."""
        cur = _bad3(adj)
        t_start = time.monotonic()
        span = max(1e-3, end - t_start)
        T0 = 1.5
        while cur > 0:
            now = time.monotonic()
            if now >= end:
                return False
            frac = (now - t_start) / span
            T = 0.05 + T0 * (1.0 - frac)
            undo = []
            r = rng.random()
            if r < 0.45 or not var:
                pr = pick_pair()
                if pr is None:
                    continue
                link(pr[0], pr[1])
                undo.append((0, pr[0], pr[1]))
            elif r < 0.7:
                u, w = var[rng.randrange(len(var))]
                unlink(u, w)
                undo.append((1, u, w))
            else:
                u, w = var[rng.randrange(len(var))]
                unlink(u, w)
                x = u if rng.random() < 0.5 else w
                y = pick_partner(x)
                if y is None:
                    link(u, w)
                    continue
                link(x, y)
                undo.append((1, u, w))
                undo.append((0, x, y))
            c2 = _bad3(adj)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
            else:
                for typ, a, b in reversed(undo):
                    if typ == 0:
                        unlink(a, b)
                    else:
                        link(a, b)
        return True

    best_n = n0
    best_E = list(E)
    while time.monotonic() < deadline:
        adj.append(set())
        adj.append(set())
        side.append(0)
        side.append(1)
        if not anneal(deadline):
            break
        best_n = len(adj)
        best_E = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return best_n, best_E


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
# Simulated annealing over bi-Cayley voltage lifts (from parent).
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
    deadline = start + 0.8 * time_limit
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
        base = _arc_base(d, random.Random(seed * 7919 + d), start + 0.2 * time_limit)
        if base is not None:
            consider(base[0], base[1])
            if D == 3:
                try:
                    n2, e2 = _grow_arcs(base, d, start + 0.6 * time_limit, rng)
                    consider(n2, e2)
                except Exception:
                    pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base_k = best_n // (2 * k)
        G = max(2, base_k + 1 + rng.randrange(0, max(3, base_k // 8 + 1)))
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
