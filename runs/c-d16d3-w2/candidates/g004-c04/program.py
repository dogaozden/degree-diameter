import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Unchanged from parent.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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


def _local_search(m, s, nbr, S, rng, deadline, iters):
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
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4). Unchanged from parent.
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
# NEW construction: Haar graphs over groups from covering difference sets.
#
# Let G be a finite group of order m, S a subset of G with |S| = d.
# H(G, S): vertices a_g and b_h (g, h in G), a_g ~ b_{g s} for s in S.
# Max degree d. Every a-a pair is joined by a path of length 2 exactly when
# the set P = { s t^{-1} : s, t in S } equals G. Then
#   a-a and b-b distances are <= 2,
#   a-b distances are <= 3 (path a_g - b_{gs} - a_{g s t^{-1}} - b_{g s t^{-1} u}).
# So diameter 3 holds with order 2|G|. The search finds S by simulated annealing
# on the number of uncovered elements of P, with O(d) incremental updates.
# For d = 16 the Moore cap is m <= 1 + 15 + 225 = 241, i.e. order 482.
# ----------------------------------------------------------------------------

def _group_candidates(m, rng):
    """(mul, inv) for cyclic Z_m and a few semidirect products Z_a x| Z_b with a*b = m."""
    gs = [lib.cyclic_group(m)[1:]]
    for b in range(2, m):
        if m % b:
            continue
        a = m // b
        if a < 2:
            continue
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
        rng.shuffle(rs)
        for r in rs[:2]:
            try:
                gs.append(lib.semidirect_group(a, b, r)[1:])
            except ValueError:
                pass
    return gs


def _tables(m, mulf, invf):
    mul = [[mulf(x, y) for y in range(m)] for x in range(m)]
    inv = [invf(x) for x in range(m)]
    return mul, inv


def _update(cnt, mul, inv, T, x, sign, covered):
    """Add (sign=+1) or remove (sign=-1) x from a set, given the other members T.

    cnt[c] counts ordered pairs (s, t) of the full set with s t^{-1} = c.
    Returns the updated number of covered values.
    """
    mx = mul[x]
    ix = inv[x]
    cells = [mx[ix]]
    for t in T:
        cells.append(mx[inv[t]])
        cells.append(mul[t][ix])
    if sign > 0:
        for c in cells:
            if cnt[c] == 0:
                covered += 1
            cnt[c] += 1
    else:
        for c in cells:
            cnt[c] -= 1
            if cnt[c] == 0:
                covered -= 1
    return covered


def _cover_search(m, d, mul, inv, rng, deadline):
    """Find S of size d in G with S S^{-1} = G, or return None by the deadline."""
    while time.monotonic() < deadline:
        cnt = [0] * m
        S = []
        covered = 0
        for x in rng.sample(range(m), d):
            covered = _update(cnt, mul, inv, S, x, 1, covered)
            S.append(x)
        temp = 0.8
        for step in range(40000):
            if covered == m:
                return S
            if (step & 255) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(d)
            old = S[i]
            x = rng.randrange(m)
            if x in S:
                continue
            T = S[:i] + S[i + 1:]
            c1 = _update(cnt, mul, inv, T, old, -1, covered)
            c2 = _update(cnt, mul, inv, T, x, 1, c1)
            if c2 >= covered or rng.random() < math.exp((c2 - covered) / temp):
                S[i] = x
                covered = c2
            else:
                _update(cnt, mul, inv, T, x, -1, c2)
                _update(cnt, mul, inv, T, old, 1, c1)
            temp = max(0.05, temp * 0.9998)
        if covered == m:
            return S
    return None


def _haar_edges(m, mul, S):
    return [(g, m + mul[g][s]) for g in range(m) for s in S]


def _haar_search(d, lo, hi, deadline, rng, consider):
    """Try orders 2m for m = lo..hi ascending, each with a time slice; consider every hit."""
    for m in range(lo, hi + 1):
        now = time.monotonic()
        if now > deadline:
            break
        budget = (deadline - now) / (hi - m + 1)
        budget = min(max(budget, 0.05), 3.0)
        groups = _group_candidates(m, rng)
        if not groups:
            continue
        per = budget / len(groups)
        for mulf, invf in groups:
            if time.monotonic() > deadline:
                break
            t_end = min(deadline, time.monotonic() + per)
            mul, inv = _tables(m, mulf, invf)
            S = _cover_search(m, d, mul, inv, rng, t_end)
            if S is not None:
                consider(2 * m, _haar_edges(m, mul, S))
                break


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (unchanged from parent).
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
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
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
        # 1. Arc-extended projective plane graphs (short budget).
        arc_deadline = start + 0.12 * T
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

        # 2. New: Haar graphs from covering difference sets over groups of order m.
        #    Order 2m; diameter 3 for any D >= 3. Ascending m from just above the best so far.
        hi = 1 + (d - 1) + (d - 1) ** 2
        lo = max(d, best_n // 2 + 1)
        haar_deadline = start + (0.55 if D == 3 else 0.35) * T
        if lo <= hi:
            _haar_search(d, lo, hi, haar_deadline, rng, consider)

    # 3. Generalized quadrangle for D >= 4.
    if D >= 4 and time.monotonic() < start + 0.5 * T:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # 4. Annealed group voltage lifts with the remaining time (parent search).
    deadline = start + 0.85 * T
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
