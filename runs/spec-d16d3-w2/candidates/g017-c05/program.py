import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction A (D = 3): PG(2, q) incidence graph extended by arcs.
#
# The incidence graph of PG(2, q) is (q+1)-regular. Let s = d - q - 1 and pick
#   S_A: points, with every line containing at most s of them,
#   S_B: lines,  with every point lying on at most s of them.
# Add an A-vertex per P in S_A, joined to the q+1 lines through P, and a
# B-vertex per L in S_B, joined to the q+1 points on L. All degrees stay <= d.
# Diameter stays 3 for any such S_A, S_B: A-A via the joining line, A-B via the
# line through P that meets L, and the old incidence graph is already diameter 3.
# Order is 2(q^2+q+1) + |S_A| + |S_B|. Leftover slack is filled with extra X-Y
# edges, which only shorten distances.
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    return m, edges, point_lines, line_points, index


def _max_load(S, groups, size):
    """Largest number of chosen elements sharing one constraint."""
    cnt = [0] * size
    for x in S:
        for y in groups[x]:
            cnt[y] += 1
    return max(cnt, default=0)


def _greedy_arc(m, s, groups, rng, trials, deadline):
    """Randomized greedy: pick elements so that every constraint is hit at most s times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cnt = [0] * m
        S = []
        for x in order:
            if all(cnt[y] < s for y in groups[x]):
                S.append(x)
                for y in groups[x]:
                    cnt[y] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _best_arc(q, m, index, groups, s, rng, deadline):
    """Largest valid choice found among greedy and conic candidates."""
    cands = [_greedy_arc(m, s, groups, rng, 60, deadline), _conic(q, index)]
    ok = [c for c in cands if c and _max_load(c, groups, m) <= s]
    return max(ok, key=len, default=[])


def _ext_graph(m, edges, point_lines, SA, SB, line_points):
    """Build PG(2,q) plus A-vertices (for SA, joined to lines through P) and B-vertices (for SB, joined to points on L)."""
    kA = len(SA)
    n = 2 * m + kA + len(SB)
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        y = 2 * m + kA + t
        for Q in line_points[j]:
            E.append((Q, y))
    return n, E, kA


def _saturate(n, edges, m, kA, d, rng):
    """Add missing X-Y edges between vertices with spare degree. Keeps bipartiteness and never lengthens distances."""
    E = set((min(u, v), max(u, v)) for u, v in edges)
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + kA]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + kA]
    pairs = [(x, y) for x in X if deg[x] < d for y in Y if deg[y] < d]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (min(x, y), max(x, y))
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the arc-extended PG(2,q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index = _pg(q)
        SA = _best_arc(q, m, index, point_lines, s, rng, deadline)
        SB = _best_arc(q, m, index, line_points, s, rng, deadline)
        n, E, kA = _ext_graph(m, edges, point_lines, SA, SB, line_points)
        out.append(_saturate(n, E, m, kA, d, rng))
    return out


# ----------------------------------------------------------------------------
# Construction B (D = 3): Haar graphs from difference covers.
#
# H(m, S) has parts Z_m, with a_i ~ b_{i+s} for s in S, so it is |S|-regular.
# It has diameter 3 exactly when S - S = Z_m. Search S by annealing on the
# number of uncovered differences, and binary-search then climb on m.
# ----------------------------------------------------------------------------

def _cover_search(k, m, rng, deadline):
    """Find S subset of Z_m, |S| = k, with S - S = Z_m. Return sorted S or None."""
    if m < k:
        return None
    if m == k:
        return list(range(m))
    S = rng.sample(range(m), k)
    in_s = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 1.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 150000 == 0:
            T = 0.5
        T = max(0.05, T * 0.9999)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        for s in others:
            g = (x - s) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = (s - x) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        for s in others:
            g = (y - s) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = (s - y) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            for s in others:
                cnt[(y - s) % m] -= 1
                cnt[(s - y) % m] -= 1
            for s in others:
                cnt[(x - s) % m] += 1
                cnt[(s - x) % m] += 1
    return sorted(S)


def _haar_search(k, rng, deadline):
    """Binary-search the largest feasible m in [k, k(k-1)+1], then climb. Return (m, S)."""
    mmax = k * (k - 1) + 1
    best = (k, list(range(k)))
    lo, hi = k, mmax
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        now = time.monotonic()
        sl = max(0.3, (deadline - now) / 5.0)
        S = _cover_search(k, mid, rng, min(deadline, now + sl))
        if S is not None:
            best = (mid, S)
            lo = mid
        else:
            hi = mid - 1
    m = best[0] + 1
    fails = 0
    while m <= mmax and time.monotonic() < deadline and fails < 2:
        now = time.monotonic()
        sl = max(0.3, (deadline - now) / 4.0)
        S = _cover_search(k, m, rng, min(deadline, now + sl))
        if S is not None:
            best = (m, S)
            fails = 0
        else:
            fails += 1
        m += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (D = 4).
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Annealed bi-Cayley voltage lifts over semidirect products (D >= 4 fallback).
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
        return _edges_of(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * float(time_limit), float(time_limit) - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D >= 3:
        # Arc-extended PG(2,q) graphs (diameter 3, valid for all D >= 3).
        arcs = _arc_candidates(d, t0 + 0.3 * budget, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, E_c in arcs[:3]:
            consider(n_c, E_c)
        # Haar graphs from difference covers of size d (diameter 3).
        if d >= 2 and time.monotonic() < deadline:
            m, S = _haar_search(d, rng, deadline)
            n_h, E_h = lib.haar_graph(m, S)
            consider(n_h, E_h)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

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

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
