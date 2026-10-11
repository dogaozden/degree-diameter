import math
import random
import time
import itertools

import lib


# ----------------------------------------------------------------------------
# Base constructions
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _record_base(d):
    """Best diameter-3 base: PG(2, d-1) if Moore-extremal, else Araujo-Pardo-Lopez for d-2, else PG."""
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            pass
    return _best_pg(d)


def _fallback(d, D):
    """Simple graphs that are valid by construction."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2


# ----------------------------------------------------------------------------
# Difference-cover lifts: 2 base vertices, darts (0,1,g), g in S, S S^{-1} = G.
# ----------------------------------------------------------------------------

def _group_list(N, rng):
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _search(N, R, d, rng, steps, deadline):
    S = rng.sample(range(N), d)

    def uncovered(S):
        return N - len({R[a][b] for a in S for b in S})

    cost = uncovered(S)
    T = 0.6
    for _ in range(steps):
        if cost == 0:
            return S
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        new = uncovered(S)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            S[i] = old
    return S if cost == 0 else None


def _diff_cover_search(d, D, base_n, rng, deadline):
    """Return a valid (n, edges) with n > base_n found by difference-cover lifts, or None."""
    lo = base_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    best = None
    best_N = lo - 1
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _o, mul, inv in _group_list(N, rng):
            jobs.append([N, mul, inv, None])
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            N, mul, inv, R = job
            if N <= best_N:
                continue
            if R is None:
                R = _ratio_table(N, mul, inv)
                job[3] = R
            S = _search(N, R, d, rng, 1200, deadline)
            if S is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
                jobs = [j for j in jobs if j[0] > best_N]
                break
        jobs = [j for j in jobs if j[0] > best_N]
    return best


# ----------------------------------------------------------------------------
# Repair growth: insert two vertices by swapping out a matching of size d.
# Works on any d-regular bipartite graph; keeps degrees <= d.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _repair_add_pair(n, edges, d, D, deadline, rng):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    Ecol = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    m_e = len(Ecol)
    if m_e < d:
        return None

    order = list(range(m_e))
    rng.shuffle(order)
    M = []
    usedA, usedB = set(), set()
    for j in order:
        a, b = Ecol[j]
        if a in usedA or b in usedB:
            continue
        M.append(j)
        usedA.add(a)
        usedB.add(b)
        if len(M) == d:
            break
    if len(M) < d:
        return None

    def make(Mlist):
        rem = set(Mlist)
        out = [Ecol[j] for j in range(m_e) if j not in rem]
        x, y = n, n + 1
        for j in Mlist:
            a, b = Ecol[j]
            out.append((x, b))
            out.append((a, y))
        return n + 2, out

    def cost(Mlist):
        nn, out = make(Mlist)
        return lib.bad_pairs(nn, out, D)

    cur = cost(M)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0 = 1.0
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - start) / span
        T = T0 * (0.02 ** frac)
        p = rng.randrange(d)
        old = M[p]
        a_old, b_old = Ecol[old]
        Mset = set(M)
        j = None
        for _ in range(60):
            c = rng.randrange(m_e)
            if c in Mset:
                continue
            a, b = Ecol[c]
            if a != a_old and a in usedA:
                continue
            if b != b_old and b in usedB:
                continue
            j = c
            break
        if j is None:
            continue
        a, b = Ecol[j]
        M2 = M[:]
        M2[p] = j
        c2 = cost(M2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            usedA.discard(a_old)
            usedB.discard(b_old)
            usedA.add(a)
            usedB.add(b)
            M = M2
            cur = c2

    if cur == 0:
        return make(M)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# ----------------------------------------------------------------------------

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


def _local_improve(m, s, point_lines, line_points, S, rng, deadline, iters):
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m

    def add(P):
        inS[P] = True
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def rem(P):
        inS[P] = False
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fits(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    cur = list(S)
    for P in cur:
        add(P)
    best = list(cur)
    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            add(P)
            cur.append(P)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        R = cur[idx]
        rem(R)
        if fits(P):
            add(P)
            cur[idx] = P
        else:
            add(R)
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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


def _arc_extensions(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _local_improve(m, s, point_lines, line_points, g, rng, deadline, 3000)
            cands.append(g)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over Z_m x| Z_k2, annealed (generic D >= 3).
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
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        # Moore-extremal case: nothing to beat.
        if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best

        if D < 3 or d < 3:
            return best

        if D == 3:
            # 1. Record base (Araujo-Pardo-Lopez or PG fallback).
            base = _record_base(d)
            if base is not None:
                consider(*base)

            # 2. Repair growth directly on the best graph.
            t_end = start + 0.35 * total
            cur = best
            while time.monotonic() < t_end:
                r = _repair_add_pair(cur[0], cur[1], d, D, t_end, rng)
                if r is None or not lib.is_valid(r[0], r[1], d, D):
                    break
                cur = r
                consider(*r)

            # 3. Difference-cover lifts with order above the current best / 2.
            t_end = start + 0.55 * total
            res = _diff_cover_search(d, D, best[0], rng, t_end)
            if res is not None:
                consider(*res)

            # 4. Arc-extended projective planes.
            t_end = start + 0.65 * total
            for n_c, e_c in _arc_extensions(d, t_end, random.Random(seed * 7919 + d)):
                consider(n_c, e_c)

        # 5. Annealed group voltage lifts for the remaining time (all D >= 3).
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base_n = best[0]
            base = base_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=1200)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
