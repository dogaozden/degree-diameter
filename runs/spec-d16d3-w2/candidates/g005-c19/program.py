import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore-type helpers
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
    return n, E


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the arc-extended PG(2,q) graph."""
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
        n, E = _arc_graph(m, edges, point_lines, line_points, S)
        out.append((n, E, None))
    return out


# ----------------------------------------------------------------------------
# D = 3: Haar graphs over abelian groups from difference covers.
#
# For an abelian group G of order m and S of size k, H(G,S) has parts
# A = G and B = G with a_g ~ b_{g+s} for s in S. It is k-regular and bipartite.
# Diameter 3 holds exactly when S - S = G (a difference cover): A-A pairs
# meet at distance <= 2, and mixed pairs at distance <= 3. The order is 2m.
# Groups Z_a x Z_b (a | b) are searched, so non-cyclic groups are allowed.
# ----------------------------------------------------------------------------

def _abelian_types(m):
    """All invariant-factor forms (a, b) with a*b = m and a | b; cyclic (1, m) first."""
    out = []
    a = 1
    while a * a <= m:
        if m % a == 0 and (m // a) % a == 0:
            out.append((a, m // a))
        a += 1
    return out


def _diff_table(a, b):
    """dt[u][v] = u - v in Z_a x Z_b, element u coded as x*b + y."""
    m = a * b
    xs = [u // b for u in range(m)]
    ys = [u % b for u in range(m)]
    return [[((xs[u] - xs[v]) % a) * b + (ys[u] - ys[v]) % b for v in range(m)]
            for u in range(m)]


def _cover(k, dt, m, rng, deadline, chunk=60000):
    """Simulated annealing for S with |S| = k and S - S = G. Returns sorted S or None."""
    while time.monotonic() < deadline:
        S = rng.sample(range(m), k)
        in_s = [False] * m
        for s in S:
            in_s[s] = True
        cnt = [0] * m
        for x in S:
            row = dt[x]
            for y in S:
                if x != y:
                    cnt[row[y]] += 1
        unc = sum(1 for g in range(1, m) if cnt[g] == 0)
        T = 0.6
        for it in range(chunk):
            if unc == 0:
                return sorted(S)
            if (it & 1023) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(k)
            x = S[i]
            y = rng.randrange(m)
            if in_s[y]:
                continue
            others = S[:i] + S[i + 1:]
            dx = dt[x]
            dy = dt[y]
            delta = 0
            for s in others:
                g = dx[s]
                cnt[g] -= 1
                if cnt[g] == 0:
                    delta += 1
                g = dt[s][x]
                cnt[g] -= 1
                if cnt[g] == 0:
                    delta += 1
            for s in others:
                g = dy[s]
                if cnt[g] == 0:
                    delta -= 1
                cnt[g] += 1
                g = dt[s][y]
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
                    cnt[dy[s]] -= 1
                    cnt[dt[s][y]] -= 1
                for s in others:
                    cnt[dx[s]] += 1
                    cnt[dt[s][x]] += 1
            T = max(0.2, T * 0.99997)
        if unc == 0:
            return sorted(S)
    return None


def _abelian_haar(a, b, S):
    """Haar graph over Z_a x Z_b: a_g ~ b_{g+s}; returns (2m, edges)."""
    m = a * b
    E = []
    for g in range(m):
        gx, gy = divmod(g, b)
        for s in S:
            sx, sy = divmod(s, b)
            h = ((gx + sx) % a) * b + (gy + sy) % b
            E.append((g, m + h))
    return 2 * m, E


def _haar_search(k, rng, deadline):
    """Ascend m from a high start; keep the largest m with a difference cover. Returns (m, a, b, S) or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    lo = max(k, int(0.8 * mmax))
    best = None
    for m in range(lo, mmax + 1):
        if time.monotonic() >= deadline:
            break
        found = None
        for a, b in _abelian_types(m):
            now = time.monotonic()
            if now >= deadline:
                break
            dt = _diff_table(a, b)
            S = _cover(k, dt, m, rng, min(deadline, now + 1.0))
            if S is not None:
                found = (a, b, S)
                break
        if found is not None:
            best = (m, found[0], found[1], found[2])
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
    end = start + max(1.0, min(0.8 * float(time_limit), float(time_limit) - 6.0))
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
        # Arc-extended projective plane (cheap, gives the known record for d = 16).
        arc_end = start + 0.25 * (end - start)
        cands = _arc_candidates(d, arc_end, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:3]:
            consider(n_c, E_c)
        # Main search: Haar graphs over abelian groups from difference covers.
        if d >= 2:
            res = _haar_search(d, rng, end)
            if res is not None:
                m, a, b, S = res
                n, E = _abelian_haar(a, b, S)
                consider(n, E)

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
