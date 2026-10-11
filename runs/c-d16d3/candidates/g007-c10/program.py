import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base for D = 3: arc-extended projective plane incidence graphs (as in parent).
#
# PG(2, q) incidence, plus one new A-vertex per SA point (joined to the q+1 lines
# through it) and one new B-vertex per SB line (joined to its q+1 points).
# Every line/point may take at most s = d-q-1 new neighbours.
#
# NEW STAGE (bold change): vertex insertion on top of the arc base.
# Adding a vertex never shortens-away existing distances, so the only condition
# for a new vertex X to be valid is that its neighbourhood N (opposite side,
# with spare degree) reaches, within 3 steps, every existing vertex:
#   - every same-side vertex is adjacent to some member of N   (distance 2)
#   - every opposite-side vertex is in N or adjacent to a vertex at distance 2 (distance 3)
# This is a randomized greedy set-cover over bitmasks, instead of the parent's
# annealed voltage lifts, which never beat the arc base for this target.
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
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
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
# Vertex insertion with bitmask set cover.
# ----------------------------------------------------------------------------

def _sides(n, E):
    adj = lib.adjacency(n, E)
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    st.append(v)
    return side


def _insert_search(d, n, E, deadline, rng):
    """Repeatedly try to add a vertex on either side whose neighbourhood reaches everything within 3."""
    side = _sides(n, E)
    adj = [0] * n
    nbr = [[] for _ in range(n)]
    for u, v in E:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
        nbr[u].append(v)
        nbr[v].append(u)
    SM = [0, 0]
    for v in range(n):
        SM[side[v]] |= 1 << v
    E = list(E)
    fails = 0
    while time.monotonic() < deadline and fails < 300:
        s = rng.randrange(2)
        opp = 1 - s
        SN, SO = SM[s], SM[opp]
        cands = [v for v in range(n) if side[v] == opp and len(nbr[v]) < d]
        if not cands:
            fails += 1
            continue
        chosen = []
        A1 = 0   # same-side vertices at distance 2 from the new vertex
        A2 = 0   # opposite-side vertices at distance 3
        Nm = 0
        for _ in range(d):
            if (A1 & SN) == SN and ((A2 | Nm) & SO) == SO:
                break
            best, bs = -1, -1.0
            for c in cands:
                if (Nm >> c) & 1:
                    continue
                a2 = A2
                t = adj[c] & ~A1
                while t:
                    lb = t & -t
                    a2 |= adj[lb.bit_length() - 1]
                    t ^= lb
                sc = (((A1 | adj[c]) & SN).bit_count()
                      + ((a2 | Nm | (1 << c)) & SO).bit_count()
                      + rng.random() * 0.9)
                if sc > bs:
                    bs, best = sc, c
            if best < 0:
                break
            c = best
            t = adj[c] & ~A1
            while t:
                lb = t & -t
                A2 |= adj[lb.bit_length() - 1]
                t ^= lb
            A1 |= adj[c]
            Nm |= 1 << c
            chosen.append(c)
        ok = bool(chosen) and (A1 & SN) == SN and ((A2 | Nm) & SO) == SO
        if not ok:
            fails += 1
            continue
        x = n
        n += 1
        adj.append(0)
        nbr.append([])
        side.append(s)
        SM[s] |= 1 << x
        for c in chosen:
            adj[c] |= 1 << x
            adj[x] |= 1 << c
            nbr[c].append(x)
            nbr[x].append(c)
            E.append((c, x))
        fails = 0
    return n, E


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Annealed group voltage lifts (used for D != 3).
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


def _cost(k, G, D, darts, perms):
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        # Stage 1: arc-extended projective plane base (valid for D >= 3).
        base_deadline = start + 0.25 * time_limit
        cands = _arc_extensions(d, base_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        base = None
        for n_c, e_c in cands:
            if lib.is_valid(n_c, e_c, d, D):
                base = (n_c, e_c)
                break
        if base is not None and base[0] > best_n:
            best, best_n = base, base[0]

        # Stage 2 (bold): insertion search on top of the base.
        if base is not None:
            deadline = start + 0.85 * time_limit
            ins_rng = random.Random(seed * 104729 + 17)
            n2, e2 = _insert_search(d, base[0], base[1], deadline, ins_rng)
            consider(n2, e2)
        return best

    # Other diameters: original pipeline.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    deadline = start + 0.7 * time_limit
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
