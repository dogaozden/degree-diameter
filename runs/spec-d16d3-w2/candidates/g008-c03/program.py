import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound and projective-plane arc helpers (secondary construction for D = 3)
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
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex and a B-vertex."""
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
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the best arc-extended PG(2,q) graph."""
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
# D = 3: Haar graphs over abelian groups from difference covers.
#
# For an abelian group G and S subset of G with |S| = k, the Haar-type graph
# has parts A = G and B = G, with a_g ~ b_{g+s} for s in S. It is k-regular
# and bipartite, has 2|G| vertices, and has diameter <= 3 whenever every
# nonzero element of G is a difference s - t (S - S = G). The search anneals
# S to cover G, and climbs the group order upward. Non-cyclic groups are
# tried too, since they sometimes admit covers when cyclic ones do not.
# ----------------------------------------------------------------------------

_TABLE_CACHE = {}


def _group_tables(mods):
    """Addition and subtraction tables for Z_{n1} x ... x Z_{nr}; element 0 is the identity."""
    if mods in _TABLE_CACHE:
        return _TABLE_CACHE[mods]
    els = list(itertools.product(*[range(n) for n in mods]))
    idx = {e: i for i, e in enumerate(els)}
    m = len(els)
    neg = [idx[tuple((-c) % n for c, n in zip(e, mods))] for e in els]
    add = []
    for e in els:
        row = [idx[tuple((a + b) % n for a, b, n in zip(e, f, mods))] for f in els]
        add.append(row)
    sub = [[add[i][neg[j]] for j in range(m)] for i in range(m)]
    res = (m, add, sub)
    _TABLE_CACHE[mods] = res
    return res


def _group_list(m):
    """Candidate abelian groups of order m: cyclic first, then rank-2 products."""
    mods = [(m,)]
    for a in range(2, math.isqrt(m) + 1):
        if m % a == 0 and m // a >= a:
            mods.append((a, m // a))
    return mods


def _cover_anneal(k, m, sub, rng, deadline):
    """Find S subset of G (|G| = m, |S| = k) with S - S = G. Returns sorted indices, or None."""
    if m < k:
        return None
    S = rng.sample(range(m), k)
    inS = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[sub[a][b]] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    if unc == 0:
        return sorted(S)
    T = 0.6
    it = 0
    while unc > 0:
        it += 1
        if (it & 2047) == 0 and time.monotonic() > deadline:
            return None
        if it % 200000 == 0:
            T = 0.6
        T = max(0.08, T * 0.99995)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if y in inS:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        # Remove the differences involving x.
        for s in others:
            g = sub[x][s]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = sub[s][x]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        # Add the differences involving y.
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
            inS.discard(x)
            inS.add(y)
            unc += delta
        else:
            for s in others:
                cnt[sub[y][s]] -= 1
                cnt[sub[s][y]] -= 1
            for s in others:
                cnt[sub[x][s]] += 1
                cnt[sub[s][x]] += 1
    return sorted(S)


def _group_haar_search(k, rng, deadline):
    """Climb the group order upward; return (n, edges) for the largest Haar graph found, or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    lo = max(k, int(0.75 * mmax))
    best = None
    fails = 0
    m = lo
    while m <= mmax and time.monotonic() < deadline:
        now = time.monotonic()
        level_deadline = min(deadline, now + max(1.0, (deadline - now) / 3.0))
        found = None
        groups = _group_list(m)
        for gi, mods in enumerate(groups):
            now = time.monotonic()
            if now >= level_deadline:
                break
            gd = min(level_deadline, now + max(0.5, (level_deadline - now) / (len(groups) - gi)))
            mm, add, sub = _group_tables(mods)
            S = _cover_anneal(k, mm, sub, rng, gd)
            if S is not None:
                found = (mm, add, S)
                break
        if found is not None:
            mm, add, S = found
            edges = [(g, mm + add[g][s]) for g in range(mm) for s in S]
            best = (2 * mm, edges)
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                break
        m += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
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
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3:
        # Primary (new): Haar graphs over abelian groups from difference covers.
        try:
            res = _group_haar_search(d, rng, start + 0.72 * budget)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass
        # Secondary: arc-extended projective plane (the parent construction).
        try:
            cands = _arc_candidates(d, start + 0.9 * budget, random.Random(seed * 7919 + d))
            cands.sort(key=lambda t: -t[0])
            for n_c, E_c, _side in cands[:1]:
                consider(n_c, E_c)
        except Exception:
            pass

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
