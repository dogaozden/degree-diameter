import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Basic helpers.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _blow_up(n, adj, w):
    """Replace base vertex v by w[v] independent copies; copies of adjacent u, v are completely joined.

    Degree of a copy of v becomes the sum of neighbour weights. Bipartiteness is kept, and
    distances are preserved (copies of one vertex are at distance 2).
    """
    start = [0] * (n + 1)
    for v in range(n):
        start[v + 1] = start[v] + w[v]
    edges = []
    for u in range(n):
        for v in adj[u]:
            if u < v:
                for a in range(start[u], start[u + 1]):
                    for b in range(start[v], start[v + 1]):
                        edges.append((a, b))
    return start[n], edges


def _weight_sa(n, adj, d, until, rng, w0):
    """Maximise sum(w) over integer weights w >= 1 with sum_{x in N(u)} w[x] <= d for all u.

    Moves: increment a vertex (if all neighbours have slack), decrement with Metropolis
    acceptance, and a plateau swap (decrement v, increment a nearby x).
    Returns the best weight vector seen.
    """
    w = list(w0)
    degw = [sum(w[x] for x in adj[u]) for u in range(n)]
    total = sum(w)
    best_w = list(w)
    best_total = total
    t0 = time.monotonic()
    span = max(1e-3, until - t0)
    T = 0.4
    it = 0
    while True:
        it += 1
        if (it & 1023) == 0:
            now = time.monotonic()
            if now >= until:
                break
            T = 0.4 * (0.02 / 0.4) ** ((now - t0) / span)
        r = rng.random()
        v = rng.randrange(n)
        nb = adj[v]
        if r < 0.45:
            if all(degw[u] < d for u in nb):
                w[v] += 1
                for u in nb:
                    degw[u] += 1
                total += 1
                if total > best_total:
                    best_total = total
                    best_w = list(w)
        elif r < 0.55:
            if w[v] >= 2 and rng.random() < math.exp(-1.0 / T):
                w[v] -= 1
                for u in nb:
                    degw[u] -= 1
                total -= 1
        else:
            if w[v] < 2 or not nb:
                continue
            u = nb[rng.randrange(len(nb))]
            x = adj[u][rng.randrange(len(adj[u]))]
            if x == v:
                continue
            w[v] -= 1
            for y in nb:
                degw[y] -= 1
            nbx = adj[x]
            if all(degw[y] < d for y in nbx):
                w[x] += 1
                for y in nbx:
                    degw[y] += 1
            else:
                w[v] += 1
                for y in nb:
                    degw[y] += 1
    return best_w


# ----------------------------------------------------------------------------
# Projective plane bases and arc-extensions (diameter 3).
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large S with all loads <= s, starting from S0."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in point_lines[P] if cl[L] >= s}
        satQ = {Q for Q in line_points[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in point_lines[R])
                or any(Q in satQ for Q in line_points[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A-vertex per point of S and a new B-vertex per line of S."""
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


def _arc_bases(d, deadline, rng):
    """Arc-extended PG(2,q) graphs for the three largest prime powers q <= d - 2."""
    qs = [q for q in range(min(d - 2, 23), 1, -1) if lib.is_prime_power(q)][:3]
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        F = lib.GF(q)
        starts = [_greedy_arc(m, s, point_lines, line_points, rng, 30, now + 0.3 * share)]
        cs = _conic_set(q, index, F)
        if _loads_ok(cs, s, m, point_lines, line_points):
            starts.append(cs)
        for S0 in starts:
            t_now = time.monotonic()
            if t_now >= deadline:
                break
            sub = min(deadline, t_now + share / len(starts))
            if not _loads_ok(S0, s, m, point_lines, line_points):
                S0 = []
            S = _local_arc(m, s, point_lines, line_points, S0, rng, sub)
            if S and _loads_ok(S, s, m, point_lines, line_points):
                out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle base (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
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


def _gq_base(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Annealed bi-Cayley voltage lifts over semidirect products (base generator).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
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
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
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
        if total > limit:
            return total
    return total


def _edges_of(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_of(k, G, darts, perms)
    return None


def _group_bases(d, D, hint, deadline, rng, limit_count=6):
    out = []
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = max(1, hint // (2 * k))
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=1200)
        if res is not None:
            out.append(res)
            if len(out) >= limit_count:
                break
    return out


# ----------------------------------------------------------------------------
# Main construction.
#
# Key idea: a blow-up of a valid base graph H (each vertex v replaced by w[v]
# independent copies, copies of adjacent vertices completely joined) keeps the
# bipartition and the diameter, and its degrees equal sums of neighbour weights.
# So the task becomes maximising sum(w) subject to neighbour-weight sums <= d,
# which is solved by annealing. Arc-extended projective planes are the main
# bases for D = 3.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}, optimal for diameter 2

    best_n, best_e = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    bases = []  # entries: (n, adj, edges)

    def add_base(n, e):
        if not e:
            return
        adj = _adjacency(n, e)
        if min(len(a) for a in adj) == 0 or max(len(a) for a in adj) > d:
            return
        if not lib.is_valid(n, e, d, D):
            return
        bases.append((n, adj, e))

    # Phase 1: base graphs.
    if D >= 3:
        pg = _pg_base(d)
        if pg is not None:
            add_base(*pg)
            consider(*pg)
        arc_deadline = t0 + (0.3 if D == 3 else 0.12) * budget
        for n_c, e_c in _arc_bases(d, arc_deadline, rng):
            add_base(n_c, e_c)
    if D >= 4:
        gq = _gq_base(d)
        if gq is not None:
            add_base(*gq)
            consider(*gq)
    if D >= 4 or not bases:
        gdl = t0 + (0.3 if D >= 4 else 0.6) * budget
        hint = max(best_n, 2 * d)
        for res in _group_bases(d, D, hint, gdl, rng):
            add_base(*res)
            consider(*res)

    # Phase 2: weight annealing on every base, round robin.
    if bases:
        cur = [[1] * n for (n, _, _) in bases]
        for n, adj, e in bases:
            pass
        while time.monotonic() < deadline - 0.05:
            remaining = deadline - time.monotonic()
            for i, (n, adj, e) in enumerate(bases):
                now = time.monotonic()
                if now >= deadline:
                    break
                slice_end = min(deadline, now + max(0.3, remaining / (4 * len(bases))))
                w = _weight_sa(n, adj, d, slice_end, rng, cur[i])
                cur[i] = w
                if sum(w) > best_n:
                    N, E = _blow_up(n, adj, w)
                    consider(N, E)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
