import itertools
import math
import random
import time

import lib


_LS_ITERS = 30000
_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Stage 1: arc-extended projective plane graphs (diameter 3, from parent).
#
# Start from PG(2, q) incidence (points 0..m-1 on side 0, lines m..2m-1 on side 1).
# Each old vertex has degree q+1, so spare s = d - q - 1.
# A new side-0 vertex joins up to d lines; every line may take at most s new edges.
# A new side-1 vertex joins up to d points under the same load limit.
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
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy load-constrained set."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """PG incidence plus new side-0 vertices (on SA points) and side-1 vertices (on SB lines)."""
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
    side = [0] * m + [1] * m + [0] * na + [1] * nb
    return n, E, side


def _arc_extensions(d, deadline, rng):
    """Return list of (n, edges, side) arc-extended plane graphs."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
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
        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


def _pg_start(d):
    """Plain PG(2, q) incidence with q the largest prime power with q + 1 <= d, plus its sides."""
    qs = [q for q in range(2, d) if lib.is_prime_power(q)]
    if not qs:
        return None
    n2, E = lib.projective_plane_incidence(qs[-1])
    m = n2 // 2
    return n2, E, [0] * m + [1] * m


# ----------------------------------------------------------------------------
# Stage 2 (new, D = 3): incremental growth by covering.
#
# Let the graph be bipartite with sides 0/1. A new vertex v on side c joined to a
# set N of side 1-c vertices (each with spare degree) keeps diameter <= 3 iff the
# radius-2 balls of N cover every vertex. Adding a vertex never lengthens an old
# shortest path, so this single test is exact: the graph stays valid.
#
# The search greedily builds covering sets, and when stuck it makes plateau kicks
# (delete a vertex if the graph stays valid) and restarts from the best state.
# ----------------------------------------------------------------------------

def _ball2(n, adj):
    """Bitmask of vertices within distance 2 of each vertex."""
    B1 = [0] * n
    for v in range(n):
        mm = 1 << v
        for u in adj[v]:
            mm |= 1 << u
        B1[v] = mm
    B2 = [0] * n
    for v in range(n):
        mm = B1[v]
        for u in adj[v]:
            mm |= B1[u]
        B2[v] = mm
    return B2


def _cover_set(n, B2, deg, side, c, d, rng, full):
    """Find up to d side-(1-c) vertices with spare degree whose balls cover everything, or None."""
    pool = [x for x in range(n) if side[x] != c and deg[x] < d]
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while len(chosen) < d and covered != full and pool:
        if rng.random() < 0.1:
            cand = [x for x in pool if B2[x] & ~covered]
            if not cand:
                break
            x = rng.choice(cand)
        else:
            bestg, x = 0, -1
            for y in pool:
                g = (B2[y] & ~covered).bit_count()
                if g > bestg:
                    bestg, x = g, y
            if x < 0:
                break
        chosen.append(x)
        pool.remove(x)
        covered |= B2[x]
    return chosen if covered == full else None


def _remove(n, edges, side, u):
    """Return (k, edges, side) after deleting vertex u and compacting labels."""
    mp = [-1] * n
    k = 0
    for x in range(n):
        if x != u:
            mp[x] = k
            k += 1
    ne = [(mp[a], mp[b]) for a, b in edges if a != u and b != u]
    ns = [side[x] for x in range(n) if x != u]
    return k, ne, ns


def _grow(d, D, n, edges, side, deadline, rng):
    """Growth with plateau kicks. Returns the best valid (n, edges, side) found."""
    best = (n, list(edges), list(side))
    cn, ce, cs = n, list(edges), list(side)
    fails = 0
    while time.monotonic() < deadline:
        adj = [set() for _ in range(cn)]
        for u, v in ce:
            adj[u].add(v)
            adj[v].add(u)
        deg = [len(a) for a in adj]
        if not any(x < d for x in deg):
            break
        B2 = _ball2(cn, adj)
        full = (1 << cn) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        added = False
        for c in sides:
            for _ in range(6):
                N = _cover_set(cn, B2, deg, cs, c, d, rng, full)
                if N:
                    ce.extend((x, cn) for x in N)
                    cs.append(c)
                    cn += 1
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            if cn > best[0]:
                best = (cn, list(ce), list(cs))
            continue
        fails += 1
        if fails > 25 or cn < best[0] - 3:
            cn, ce, cs = best[0], list(best[1]), list(best[2])
            fails = 0
            continue
        for _ in range(8):
            u = rng.randrange(cn)
            k, ne, ns = _remove(cn, ce, cs, u)
            if k > 0 and lib.is_valid(k, ne, d, D):
                cn, ce, cs = k, ne, ns
                break
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4) and voltage annealing (D >= 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, or None."""
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
    """Number of (representative, vertex) pairs not reached within distance D."""
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
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    if D >= 3:
        try:
            starts = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
            pg = _pg_start(d)
            if pg is not None:
                starts.append(pg)
            starts.sort(key=lambda t: -t[0])
            for n_c, e_c, _s in starts:
                consider(n_c, e_c)

            # Growth from the best starts. Valid for any D >= 3.
            grow_end = t0 + (0.8 if D == 3 else 0.5) * time_limit
            top = starts[:2]
            for i, (n_c, e_c, s_c) in enumerate(top):
                now = time.monotonic()
                share_end = now + (grow_end - now) / (len(top) - i)
                gn, ge, _gs = _grow(d, D, n_c, e_c, s_c, share_end, rng)
                consider(gn, ge)
        except Exception:
            pass

    if D >= 4:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        deadline = t0 + 0.85 * time_limit
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
