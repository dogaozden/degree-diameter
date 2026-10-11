import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# PG(2, q) data. Points and lines share the same vector index 0..m-1.
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


# ----------------------------------------------------------------------------
# Family 1: arc-extended PG(2,q) incidence graphs (diameter 3, the parent's
# construction). Kept as a guaranteed baseline.
# ----------------------------------------------------------------------------

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
        for L in point_lines[P]:
            E.append((2 * m + t, m + L))
    for t, j in enumerate(S):
        for Q in line_points[j]:
            E.append((Q, 2 * m + k + t))
    return n, E


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        m, edges, point_lines, line_points, index, _ = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Family 2 (new, bold): cover families.
#
# Choose a point-side covers M_1..M_a, each a set of K lines covering all
# points of PG(2,q), pairwise sharing at least one line, with every line in at
# most cap = d-q-1 of the sets. Add new A_i joined to the lines of M_i and new
# B_i joined to the points with the same indices as the lines of M_i. Then:
#   A-A and B-B pairs share a line / point, A-B pairs are at distance <= 3,
#   old points reach A_i in 2 (cover), old lines reach B_i in 2 (blocking
#   property, which equals the cover property by the self-duality of the
#   dot product), and every old vertex stays within degree d.
# Order = 2(q^2+q+1) + 2a. With q = 13, d = 16 and a = 17, K = 16 this is 400,
# and pairwise sharing with load 2 forces a <= K + 1.
# ----------------------------------------------------------------------------

def _cover_search(m, point_lines, line_points, K, a, cap, deadline, rng):
    """Simulated annealing for a covers. Returns list of line lists, or None."""
    if K > m or a < 2 or cap < 1:
        return None
    M = [rng.sample(range(m), K) for _ in range(a)]
    inM = []
    for Ls in M:
        row = bytearray(m)
        for L in Ls:
            row[L] = 1
        inM.append(row)
    cov = [[0] * m for _ in range(a)]
    for i in range(a):
        ci = cov[i]
        for L in M[i]:
            for p in line_points[L]:
                ci[p] += 1
    load = [0] * m
    for Ls in M:
        for L in Ls:
            load[L] += 1
    sh = [[0] * a for _ in range(a)]
    for i in range(a):
        for k in range(a):
            if k != i:
                sh[i][k] = sum(1 for L in M[i] if inM[k][L])
    cost = (sum(1 for i in range(a) for p in range(m) if cov[i][p] == 0)
            + sum(1 for i in range(a) for k in range(i + 1, a) if sh[i][k] == 0)
            + sum(max(0, x - cap) for x in load))

    def apply(i, t, Lo, Ln):
        dU = dV = dO = 0
        ci = cov[i]
        for p in line_points[Lo]:
            ci[p] -= 1
            if ci[p] == 0:
                dU += 1
        for p in line_points[Ln]:
            if ci[p] == 0:
                dU -= 1
            ci[p] += 1
        ri = sh[i]
        for k in range(a):
            if k == i:
                continue
            ik = inM[k]
            if ik[Lo]:
                v = ri[k] - 1
                ri[k] = v
                sh[k][i] = v
                if v == 0:
                    dV += 1
            if ik[Ln]:
                v = ri[k]
                if v == 0:
                    dV -= 1
                ri[k] = v + 1
                sh[k][i] = v + 1
        if load[Lo] > cap:
            dO -= 1
        load[Lo] -= 1
        load[Ln] += 1
        if load[Ln] > cap:
            dO += 1
        inM[i][Lo] = 0
        inM[i][Ln] = 1
        M[i][t] = Ln
        return dU, dV, dO

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 1.0
    it = 0
    while cost > 0:
        it += 1
        if (it & 255) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = 1.2 * (0.07 ** (((now - t0) / span * 3.0) % 1.0))
        i = rng.randrange(a)
        t = rng.randrange(K)
        Lo = M[i][t]
        Ln = None
        if rng.random() < 0.5:
            p = rng.randrange(m)
            if cov[i][p] == 0:
                Ln = rng.choice(point_lines[p])
        if Ln is None:
            Ln = rng.randrange(m)
        if inM[i][Ln]:
            continue
        dU, dV, dO = apply(i, t, Lo, Ln)
        dc = dU + dV + dO
        if dc <= 0 or rng.random() < math.exp(-dc / T):
            cost += dc
        else:
            apply(i, t, Ln, Lo)
    return M if cost == 0 else None


def _family_graph(m, edges, M):
    a = len(M)
    E = list(edges)
    for i, Ls in enumerate(M):
        for L in Ls:
            E.append((2 * m + i, m + L))
        for L in Ls:
            E.append((L, 2 * m + a + i))
    return 2 * m + 2 * a, E


def _family_phase(d, deadline, rng, consider):
    q = max((x for x in range(2, d) if lib.is_prime_power(x)), default=0)
    if q < 2 or d - q - 1 < 2:
        return
    m, edges, point_lines, line_points, _, _ = _pg_data(q)
    cap = d - q - 1
    K = min(d, m)
    if K < q + 1:
        return

    def attempt(a, dl):
        M = _cover_search(m, point_lines, line_points, K, a, cap, dl, rng)
        if M is None:
            return False
        consider(*_family_graph(m, edges, M))
        return True

    t = time.monotonic()
    if attempt(K, t + 0.5 * (deadline - t)):
        attempt(K + 1, deadline)
    else:
        attempt(K - 1, deadline)


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), unchanged from parent.
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


def _voltage_phase(d, D, best_n, deadline, rng, consider):
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
            arc_rng = random.Random(seed * 7919 + d)
            for n_c, e_c in _arc_candidates(d, start + 0.25 * time_limit, arc_rng):
                consider(n_c, e_c)
        except Exception:
            pass
        try:
            _family_phase(d, deadline, rng, consider)
        except Exception:
            pass

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    if D != 3:
        try:
            _voltage_phase(d, D, best_n, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
