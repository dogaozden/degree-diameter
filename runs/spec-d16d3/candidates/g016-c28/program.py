import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3), with a search over the
# extension sets and a greedy vertex-augmentation pass.
#
# Base: incidence graph of PG(2, q) (points 0..m-1 colour 0, lines m..2m-1 colour 1).
# Two index sets are chosen independently:
#   SA (points): each P in SA gets a new colour-0 vertex joined to the q+1 lines through P.
#   SB (lines):  each j in SB gets a new colour-1 vertex joined to the q+1 points on j.
# Constraints: every line lies on at most s = d-q-1 points of SA, and every point
# lies on at most s lines of SB, so no old vertex exceeds degree d.
#
# Augmentation: a new vertex v of colour c, joined to a set X of opposite-colour
# vertices with spare degree, keeps diameter 3 iff N(X) contains every colour-c
# vertex (then distance 2 covers colour c and distance 3 covers the rest). Any
# such X is accepted, so the graph is always valid by construction. Extra
# vertices are found greedily and the SA/SB sets are improved by local search.
# ----------------------------------------------------------------------------

_PG_CACHE = {}


def _pg_data(q):
    """Return (m, point_lines, line_points, index, pts) for PG(2, q), cached."""
    if q not in _PG_CACHE:
        pts = lib.projective_points(q)
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        point_lines = [[] for _ in range(m)]
        line_points = [[] for _ in range(m)]
        for u, v in edges:
            point_lines[u].append(v - m)
            line_points[v - m].append(u)
        index = {p: i for i, p in enumerate(pts)}
        _PG_CACHE[q] = (m, point_lines, line_points, index, pts)
    return _PG_CACHE[q]


def _loads(SA, SB, m, point_lines, line_points):
    """cl[L] = number of SA points on line L; cp[Q] = number of SB lines through point Q."""
    cl = [0] * m
    cp = [0] * m
    for P in SA:
        for L in point_lines[P]:
            cl[L] += 1
    for j in SB:
        for Q in line_points[j]:
            cp[Q] += 1
    return cl, cp


def _fill(SA, SB, s, m, point_lines, line_points, rng):
    """Greedily add random feasible indices to SA and SB in place; all loads stay <= s."""
    cl, cp = _loads(SA, SB, m, point_lines, line_points)
    cands = [('A', P) for P in range(m) if P not in SA]
    cands += [('B', j) for j in range(m) if j not in SB]
    rng.shuffle(cands)
    for kind, x in cands:
        if kind == 'A':
            if all(cl[L] < s for L in point_lines[x]):
                SA.add(x)
                for L in point_lines[x]:
                    cl[L] += 1
        else:
            if all(cp[Q] < s for Q in line_points[x]):
                SB.add(x)
                for Q in line_points[x]:
                    cp[Q] += 1


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, point_lines, line_points, SA, SB):
    """Return (n, edges, colours) for the PG incidence graph plus A- and B-vertices."""
    SAl = sorted(SA)
    SBl = sorted(SB)
    E = [(P, m + L) for P in range(m) for L in point_lines[P]]
    colours = [0] * m + [1] * m
    for t, P in enumerate(SAl):
        x = 2 * m + t
        colours.append(0)
        E.extend((x, m + L) for L in point_lines[P])
    off = 2 * m + len(SAl)
    for t, j in enumerate(SBl):
        b = off + t
        colours.append(1)
        E.extend((Q, b) for Q in line_points[j])
    return off + len(SBl), E, colours


def _augment(n, E, colours, d, rng, deadline):
    """Greedily add vertices whose neighbourhood X (opposite colour, spare degree) covers all same-colour vertices.

    Such a vertex keeps diameter 3. Returns (n, edges) with the added vertices.
    """
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    E = list(E)
    colours = list(colours)
    cnt = [colours.count(0), colours.count(1)]
    while True:
        progress = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for p in order:
            if time.monotonic() > deadline:
                return len(adj), E
            X = adj[p]
            k = len(X)
            if k == 0 or k > d:
                continue
            if any(len(adj[x]) >= d for x in X):
                continue
            c = colours[p]
            cov = set()
            for x in X:
                cov.update(adj[x])
            if len(cov) != cnt[c]:
                continue
            v = len(adj)
            Xl = list(X)
            adj.append(Xl)
            colours.append(c)
            cnt[c] += 1
            for x in Xl:
                adj[x].append(v)
                E.append((x, v))
            progress = True
        if not progress:
            return len(adj), E


def _score(SA, SB, d, data, rng, deadline):
    m, point_lines, line_points, _, _ = data
    n, E, col = _arc_graph(m, point_lines, line_points, SA, SB)
    return _augment(n, E, col, d, rng, deadline)


def _local_search(d, s, data, rng, deadline, SA, SB):
    """Hill-climb over (SA, SB) with random removals and refills; score is the augmented order."""
    m, point_lines, line_points, _, _ = data
    SA, SB = set(SA), set(SB)
    cur_n, _ = _score(SA, SB, d, data, rng, deadline)
    best_n, best_E = None, None
    best_n, best_E = _score(SA, SB, d, data, rng, deadline)
    best_n = best_n
    cur_n = best_n
    while time.monotonic() < deadline:
        nA, nB = set(SA), set(SB)
        for _ in range(rng.choice([1, 1, 2, 2, 3])):
            if nA and (not nB or rng.random() < 0.5):
                nA.remove(rng.choice(sorted(nA)))
            elif nB:
                nB.remove(rng.choice(sorted(nB)))
        _fill(nA, nB, s, m, point_lines, line_points, rng)
        n2, E2 = _score(nA, nB, d, data, rng, deadline)
        if n2 >= cur_n or rng.random() < 0.03:
            SA, SB, cur_n = nA, nB, n2
        if n2 > best_n:
            best_n, best_E = n2, E2
    return best_n, best_E


def _arc_phase(d, deadline, rng):
    """Build and search arc-extended PG graphs for each prime power q with q + 1 <= d.

    Returns a list of candidate (n, edges) graphs, all with diameter 3.
    """
    ranked = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0 or time.monotonic() > deadline:
            continue
        data = _pg_data(q)
        m, point_lines, line_points, index, pts = data
        starts = []
        SA, SB = set(), set()
        _fill(SA, SB, s, m, point_lines, line_points, rng)
        starts.append((SA, SB))
        if s >= 2:
            F = lib.GF(q)
            cs = set(_conic_set(q, index, F))
            cl, cp = _loads(cs, cs, m, point_lines, line_points)
            if max(cl) <= s and max(cp) <= s:
                starts.append((cs, set(cs)))
        for SA0, SB0 in starts:
            n2, E2 = _score(SA0, SB0, d, data, rng, deadline)
            ranked.append((n2, q, s, SA0, SB0, E2))

    ranked.sort(key=lambda t: -t[0])
    results = [(t[0], t[5]) for t in ranked]

    # Search only where extension sets can change something (s >= 1).
    searchable = [t for t in ranked if t[2] >= 1]
    for idx, t in enumerate(searchable[:2]):
        now = time.monotonic()
        if now >= deadline:
            break
        share = 0.6 if idx == 0 else 0.4
        if len(searchable) == 1:
            share = 1.0
        sub = min(deadline, now + (deadline - now) * share)
        data = _pg_data(t[1])
        bn, bE = _local_search(d, t[2], data, rng, sub, t[3], t[4])
        if bE is not None:
            results.append((bn, bE))
    return results


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
# Simulated annealing over bi-Cayley voltage lifts (used for D != 3).
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
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best_n, best_g = fallback[0], fallback

    def consider(n, e):
        nonlocal best_n, best_g
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_g = n, (n, e)

    deadline = start + (0.85 if D == 3 else 0.7) * time_limit

    # Arc-extended PG graphs (diameter 3, so valid for all D >= 3). For D == 3
    # they get the whole budget; for larger D only a short slice.
    if D >= 3:
        arc_deadline = deadline if D == 3 else start + 0.3 * time_limit
        results = _arc_phase(d, arc_deadline, rng)
        results.sort(key=lambda t: -t[0])
        for n_c, e_c in results:
            if n_c > best_n:
                consider(n_c, e_c)

    if D == 3:
        if not lib.is_valid(best_g[0], best_g[1], d, D):
            best_g = fallback
        return best_g

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search for D != 3: annealed group voltage lifts. Larger bases for D >= 5.
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

    if not lib.is_valid(best_g[0], best_g[1], d, D):
        best_g = fallback
    return best_g
