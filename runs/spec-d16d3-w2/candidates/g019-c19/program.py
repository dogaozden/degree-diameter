import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc construction (kept as the safe baseline for D = 3).
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
# NEW for D = 3: cyclic Haar graphs found by difference-cover annealing.
#
# Haar graph H(Z_m, S) with |S| = d has parts a_i, b_j and a_i ~ b_j iff j - i
# is in S. It is bipartite and d-regular on 2m vertices. Diameter 3 holds iff
#   (1) S - S covers every nonzero residue mod m (same-side pairs at distance 2),
#   (2) S union (S - S + S) covers every residue mod m (opposite pairs at distance 1 or 3).
# Condition (1) is searched with an incremental annealer; (2) is checked directly.
# ----------------------------------------------------------------------------

def _swap(cnt, S, i, v, m, cost):
    """Replace S[i] by v, updating difference counts and the number of uncovered nonzero residues."""
    s = S[i]
    for j, t in enumerate(S):
        if j == i:
            continue
        x = (s - t) % m
        cnt[x] -= 1
        if cnt[x] == 0:
            cost += 1
        y = (t - s) % m
        cnt[y] -= 1
        if cnt[y] == 0:
            cost += 1
    S[i] = v
    for j, t in enumerate(S):
        if j == i:
            continue
        x = (v - t) % m
        if cnt[x] == 0:
            cost -= 1
        cnt[x] += 1
        y = (t - v) % m
        if cnt[y] == 0:
            cost -= 1
        cnt[y] += 1
    return cost


def _cover3_ok(S, m):
    """Check that S union (S - S + S) covers all of Z_m (opposite-side distance condition)."""
    T = set()
    for a in S:
        for b in S:
            ab = a - b
            for c in S:
                T.add((ab + c) % m)
    Sset = set(S)
    return all((x in Sset) or (x in T) for x in range(m))


def _find_cover(m, k, deadline, rng):
    """Anneal a k-subset S of Z_m whose differences cover Z_m \\ {0} and that passes the
    opposite-side check. Returns sorted S or None if the deadline passes."""
    if k > m or k * (k - 1) + 1 < m:
        return None
    ITER = 150000
    while time.monotonic() < deadline:
        S = rng.sample(range(m), k)
        inS = [False] * m
        for s in S:
            inS[s] = True
        cnt = [0] * m
        for a in S:
            for b in S:
                if a != b:
                    cnt[(a - b) % m] += 1
        cost = sum(1 for x in range(1, m) if cnt[x] == 0)
        T = 1.0
        decay = 0.05 ** (1.0 / ITER)
        for it in range(ITER):
            if (it & 1023) == 0 and time.monotonic() >= deadline:
                return None
            i = rng.randrange(k)
            v = rng.randrange(m)
            if inS[v]:
                continue
            s = S[i]
            c2 = _swap(cnt, S, i, v, m, cost)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                inS[s] = False
                inS[v] = True
                cost = c2
                if cost == 0 and _cover3_ok(S, m):
                    return sorted(S)
            else:
                _swap(cnt, S, i, s, m, c2)
            T *= decay
    return None


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4), unchanged from parent.
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
    deadline = start + 0.75 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D >= 3:
        cands = _arc_candidates(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands:
            consider(n_c, E_c)

    if D == 3:
        # Search cyclic Haar graphs on 2m vertices with m above the current best half-order.
        lo = best_n // 2 + 1
        hi = d * (d - 1) + 1  # Moore bound: 2(d^2 - d + 1) vertices
        search_rng = random.Random(seed * 104729 + d)
        m = lo
        while m <= hi and time.monotonic() < deadline:
            S = _find_cover(m, d, deadline, search_rng)
            if S is None:
                break
            n2, E2 = lib.haar_graph(m, S)
            if not lib.is_valid(n2, E2, d, D):
                break
            consider(n2, E2)
            m += 1

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
