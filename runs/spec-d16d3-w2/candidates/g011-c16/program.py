import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc extension (safe fallback for D = 3, reaches the record
# order for d = 16 and is kept as a comparison candidate).
# ----------------------------------------------------------------------------

def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


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


def _conic_set(q, index):
    F = lib.GF(q)
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
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E, None


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Haar-type graphs over abelian groups (D = 3).
#
# For a group G of order m and S subset of G with |S| = k, the graph with parts
# A = G, B = G and edges a_g ~ b_{g+s} (s in S) is k-regular and bipartite.
# Its diameter is at most 3 exactly when every nonzero element of G is a
# difference s - t of two elements of S (a "difference cover"). The order is 2m.
# Non-cyclic groups Z_a x Z_b (a | b) are searched alongside Z_m, since they
# sometimes admit covers where cyclic groups do not.
# ----------------------------------------------------------------------------

_OPS_CACHE = {}


def _group_ops(a, b):
    """Addition and subtraction tables for Z_a x Z_b, element x coded as (x // b) * b + x % b."""
    key = (a, b)
    if key in _OPS_CACHE:
        return _OPS_CACHE[key]
    m = a * b

    def add(x, y):
        return ((x // b + y // b) % a) * b + (x % b + y % b) % b

    neg = [((-(x // b)) % a) * b + ((-(x % b)) % b) for x in range(m)]
    sub = [[add(x, neg[y]) for y in range(m)] for x in range(m)]
    _OPS_CACHE[key] = (add, sub)
    return add, sub


def _anneal(sub, m, k, rng, deadline):
    """Find S subset of G (|S| = k) whose differences cover G \\ {0}. Returns sorted S or None."""
    S = rng.sample(range(m), k)
    in_s = [False] * m
    for s in S:
        in_s[s] = True
    cnt = [0] * m
    for x in S:
        row = sub[x]
        for y in S:
            if x != y:
                cnt[row[y]] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 0.8
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 200000 == 0:
            T = 0.8
        else:
            T = max(0.15, T * 0.9999)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if in_s[y]:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        # Remove differences involving x.
        for s in others:
            g = sub[x][s]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = sub[s][x]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        # Add differences involving y.
        for s in others:
            g = sub[y][s]
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = sub[s][y]
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s[x] = False
            in_s[y] = True
            unc += delta
        else:
            for s in others:
                cnt[sub[y][s]] -= 1
                cnt[sub[s][y]] -= 1
            for s in others:
                cnt[sub[x][s]] += 1
                cnt[sub[s][x]] += 1
    return sorted(S)


def _group_search(k, lo, seed, deadline):
    """Find the largest group order m >= lo (m <= k(k-1)+1) with a difference cover of size k.

    Returns (m, a, b, S, add) or None. Candidates are tried in rounds with doubling
    time slices, smallest m first; once a success is found only larger m are tried.
    """
    mmax = k * (k - 1) + 1
    cands = []
    for m in range(max(k + 1, lo), mmax + 1):
        for a in range(1, m + 1):
            if m % a == 0:
                b = m // a
                if b % a == 0:
                    cands.append((m, a, b))
    if not cands:
        return None
    rng = random.Random(seed)
    best = None
    slice_t = 1.0
    while time.monotonic() < deadline:
        tried = False
        for (m, a, b) in cands:
            if best is not None and m <= best[0]:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            add, sub = _group_ops(a, b)
            S = _anneal(sub, m, k, rng, min(deadline, now + slice_t))
            tried = True
            if S is not None:
                best = (m, a, b, S, add)
        if best is not None and not any(m > best[0] for (m, _, _) in cands):
            break
        if not tried:
            break
        slice_t *= 2
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4)
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * float(time_limit), 46.0)
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3:
        # Comparison candidate: arc-extended projective plane.
        arcs = _arc_candidates(d, start + 0.12 * budget, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in arcs[:1]:
            consider(n_c, E_c)

        # Main search: difference-cover Haar graphs over abelian groups.
        lo = best_n // 2 + 1
        res = _group_search(d, lo, seed * 1000003 + 17 * d + 3, deadline)
        if res is not None:
            m, a, b, S, add = res
            E = [(g, m + add(g, s)) for g in range(m) for s in S]
            consider(2 * m, E)

    elif D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
