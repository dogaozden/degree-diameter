import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Dual-arc projective plane graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q): points 0..m-1, lines m..2m-1.
# Every old vertex has degree q+1, so with d >= q+1 the spare capacity is
# s = d - q - 1. Choose a point set U with at most s points on every line, and
# a line set V with at most s lines through every point, independently.
# For each P in U add an A-vertex joined to the q+1 lines through P; for each
# j in V add a B-vertex joined to the q+1 points on j. Every such addition keeps
# diameter 3, because two A-vertices share the line PP', two B-vertices share
# a common point, and A/B pairs are joined by a path of length <= 3.
# U and V may be chosen independently (the parent coupled them with S = U = V).
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


def _max_load(chosen, targets_of, m):
    """Largest number of chosen elements sharing one target (targets_of[e] lists the targets of e)."""
    load = [0] * m
    for e in chosen:
        for t in targets_of[e]:
            load[t] += 1
    return max(load, default=0)


def _greedy_side(targets_of, m, s, rng, trials, deadline):
    """Randomized greedy: pick elements so that every target is hit at most s times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        chosen = []
        for e in order:
            tg = targets_of[e]
            if all(load[t] < s for t in tg):
                chosen.append(e)
                for t in tg:
                    load[t] += 1
        if len(chosen) > len(best):
            best = chosen
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _best_side(targets_of, m, s, rng, deadline, extra):
    """Largest valid choice on one side: random greedy or one of the given structured sets."""
    if s < 1:
        return []
    cands = [_greedy_side(targets_of, m, s, rng, 40, deadline)]
    for X in extra:
        if X is not None and _max_load(X, targets_of, m) <= s:
            cands.append(X)
    return max(cands, key=len)


def _dual_arc_graph(m, edges, point_lines, line_points, U, V):
    """Old PG incidence plus an A-vertex per point of U and a B-vertex per line of V."""
    n = 2 * m + len(U) + len(V)
    E = list(edges)
    for t, P in enumerate(U):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    base_b = 2 * m + len(U)
    for t, j in enumerate(V):
        b = base_b + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _dual_arc_candidates(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        extra = []
        if s >= 2:
            F = lib.GF(q)
            extra.append(_conic_set(q, index, F))
        U = _best_side(point_lines, m, s, rng, deadline, extra)
        V = _best_side(line_points, m, s, rng, deadline, extra)
        out.append(_dual_arc_graph(m, edges, point_lines, line_points, U, V))
    return out


# ----------------------------------------------------------------------------
# Greedy cover fill (diameter 3).
#
# A new vertex x on one side is at distance 2 from every vertex of its own side
# only if its neighbourhood T covers that side. We pick T by randomized greedy
# (noise below 1 never overrides a larger coverage gain) among opposite-side
# vertices with spare degree, then accept x only if lib.is_valid still passes.
# The validity check is exact, so the output is always valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _greedy_cover(adj, cands, uncovered, d, rng):
    """Pick at most d candidates whose neighbourhoods cover all of `uncovered`, or None."""
    unc = set(uncovered)
    chosen = []
    pool = list(cands)
    while unc and len(chosen) < d:
        best_v, best_key = -1, None
        for v in pool:
            g = 0
            for u in adj[v]:
                if u in unc:
                    g += 1
            if g == 0:
                continue
            key = g + rng.random() * 0.99
            if best_key is None or key > best_key:
                best_key, best_v = key, v
        if best_v < 0:
            return None
        chosen.append(best_v)
        pool.remove(best_v)
        for u in adj[best_v]:
            unc.discard(u)
    return None if unc else chosen


def _fill_fast(n, edges, d, D, deadline, rng, tries=6):
    """Repeatedly add a vertex whose neighbourhood covers one side, keeping validity."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 300:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        progressed = False
        for _ in range(tries):
            c = rng.randrange(2)
            uncovered = [v for v in range(n) if col[v] == 1 - c]
            cand = [v for v in range(n) if col[v] == c and deg[v] < d]
            ch = _greedy_cover(adj, cand, uncovered, d, rng)
            if ch is None:
                continue
            new_edges = edges + [(v, n) for v in ch]
            if lib.is_valid(n + 1, new_edges, d, D):
                edges = new_edges
                n += 1
                progressed = True
                break
        fails = 0 if progressed else fails + 1
    return n, edges


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
# Simulated annealing over bi-Cayley voltage lifts.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
    deadline = start + 0.7 * time_limit
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
        # Dual-arc constructions: valid for all D >= 3 by the argument above.
        cands = _dual_arc_candidates(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

        # Cover-fill the largest few candidates; every addition is checked exactly.
        fill_end = start + 0.55 * time_limit
        top = cands[:3]
        for idx, (n_c, e_c) in enumerate(top):
            now = time.monotonic()
            if now >= fill_end:
                break
            share = (fill_end - now) / (len(top) - idx)
            n_f, e_f = _fill_fast(n_c, e_c, d, D, now + share,
                                  random.Random(seed * 104729 + d + idx))
            consider(n_f, e_f)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts. For D >= 5 use larger bases.
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
