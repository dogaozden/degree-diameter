import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold D = 3 construction: bipartite Cayley graphs over finite groups.
#
# For a group G of order M and a d-subset S of G, the graph on parts A = G and
# B = G with edges a_g ~ b_{g s} (s in S) is d-regular on 2M vertices. Distance
# between two A-vertices is at most 2 when S S^{-1} = G, and then every mixed
# pair is within distance 3 because G = S S^{-1} implies G = S S^{-1} S. So the
# search anneals S to make S S^{-1} cover all of G, over cyclic and
# semidirect-product groups of orders above the known record.
#
# Fallbacks: the arc-extended projective plane (order 2(m + k)) and K_{d,d}.
# Every candidate is verified with lib.is_valid before it is kept.
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


def _groups(M):
    """Return groups of order M as (order, mul, inv) triples: cyclic plus a few semidirect products."""
    out = [lib.cyclic_group(M)]
    for k in range(2, M):
        if M % k:
            continue
        m = M // k
        if m < 2:
            continue
        cnt = 0
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            try:
                out.append(lib.semidirect_group(m, k, r))
            except ValueError:
                continue
            cnt += 1
            if cnt >= 3:
                break
    return out


def _tables(order, mul, inv):
    """Multiplication table and inverse list for a group on 0..order-1."""
    mt = [[mul(a, b) for b in range(order)] for a in range(order)]
    iv = [inv(a) for a in range(order)]
    return mt, iv


def _anneal(mt, iv, M, k, rng, deadline):
    """Find S of size k with {t s^{-1} : s, t in S} = G, or return None at the deadline."""
    e = mt[0][iv[0]]
    S = rng.sample(range(M), k)
    inS = [False] * M
    for s in S:
        inS[s] = True
    cnt = [0] * M
    for s in S:
        for t in S:
            cnt[mt[t][iv[s]]] += 1
    unc = sum(1 for g in range(M) if cnt[g] == 0)
    if unc == 0:
        return sorted(S)
    T = 0.6
    it = 0
    c = cnt
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        if (it % 200000) == 0:
            T = 0.6
        T = max(0.12, T * 0.99995)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(M)
        if inS[y]:
            continue
        O = [S[j] for j in range(k) if j != i]
        # Remove x's pairs.
        delta = 0
        c[e] -= 1
        if c[e] == 0:
            delta += 1
        for s in O:
            g = mt[x][iv[s]]
            c[g] -= 1
            if c[g] == 0:
                delta += 1
            g = mt[s][iv[x]]
            c[g] -= 1
            if c[g] == 0:
                delta += 1
        # Add y's pairs.
        if c[e] == 0:
            delta -= 1
        c[e] += 1
        for s in O:
            g = mt[y][iv[s]]
            if c[g] == 0:
                delta -= 1
            c[g] += 1
            g = mt[s][iv[y]]
            if c[g] == 0:
                delta -= 1
            c[g] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS[x] = False
            inS[y] = True
            unc += delta
            if unc == 0:
                return sorted(S)
        else:
            # Revert the addition of y, then the removal of x.
            c[e] -= 1
            for s in O:
                c[mt[y][iv[s]]] -= 1
                c[mt[s][iv[y]]] -= 1
            c[e] += 1
            for s in O:
                c[mt[x][iv[s]]] += 1
                c[mt[s][iv[x]]] += 1


def _cayley_edges(M, mt, S):
    """Bipartite graph on 2M vertices: a_g = g, b_h = M + h, with a_g ~ b_{g s} for s in S."""
    return [(g, M + mt[g][s]) for g in range(M) for s in S]


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

    if D == 3 and d >= 2:
        # Arc-extended projective plane (known-good candidate).
        cands = _arc_candidates(d, start + 0.15 * budget, random.Random(seed * 7919 + d))
        if cands:
            n_c, E_c = max(cands, key=lambda t: t[0])
            consider(n_c, E_c)

        # Bold candidate: Cayley bipartite graphs with S S^{-1} = G, |S| = d.
        mmax = d * (d - 1) + 1
        lo = max(d, int(0.8 * mmax))
        for M in range(lo, mmax + 1):
            remaining = deadline - time.monotonic()
            if remaining <= 0.2:
                break
            groups = _groups(M)
            rng.shuffle(groups)
            for order, mul, inv in groups:
                remaining = deadline - time.monotonic()
                if remaining <= 0.2:
                    break
                slice_ = max(0.3, min(8.0, remaining / 3.0))
                mt, iv = _tables(order, mul, inv)
                S = _anneal(mt, iv, order, d, rng, min(deadline, time.monotonic() + slice_))
                if S is not None:
                    consider(2 * order, _cayley_edges(order, mt, S))
                    break

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
