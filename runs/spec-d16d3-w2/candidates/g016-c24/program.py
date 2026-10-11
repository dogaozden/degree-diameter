import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc-extended incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d-q-1. For a point set S with every
# line holding <= s points of S and every point on <= s lines indexed by S, add
# an A-vertex per P in S (joined to the lines through P) and a B-vertex per j in
# S (joined to the points on line j). Order 2(q^2+q+1) + 2|S|.
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
    """Randomized greedy point set with all loads <= s; returns the largest found."""
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


def _arc_graph(m, edges, S, line_points):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in _PL[0][P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


_PL = [None]


def _arc_best(d, deadline, rng):
    """Largest arc-extended PG(2,q) graph over prime powers q <= d-1, as (n, edges), or None."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp = _pg_incidence(q)
        _PL[0] = pl
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, pl, lp, rng, 40, deadline)
        if s >= 2:
            pts = lib.projective_points(q)
            index = {p: i for i, p in enumerate(pts)}
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                S = cs
        if not _loads_ok(S, s, m, pl, lp):
            continue
        n, E = _arc_graph(m, edges, S, lp)
        if best is None or n > best[0]:
            best = (n, E)
    return best


# ----------------------------------------------------------------------------
# Haar graphs from difference covers (diameter 3).
#
# H(m, S): a_i ~ b_{i+s} for s in S, |S| = k. It is k-regular and bipartite.
# If S - S = Z_m (every nonzero residue is a difference), then A-A and B-B pairs
# are at distance <= 2, and mixed pairs at distance <= 3 since S - S + S = Z_m.
# Order 2m; a cover with m >= best_n/2 + 1 beats the arc construction.
# ----------------------------------------------------------------------------

def _anneal_cover(S, k, m, rng, deadline, iters):
    """Anneal S (list of k residues) toward S - S = Z_m. Returns sorted S or None."""
    in_s = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 0.4
    for it in range(1, iters + 1):
        if unc == 0:
            return sorted(S)
        if (it & 4095) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        # Remove x's differences.
        for s in others:
            g = (x - s) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = (s - x) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        # Add y's differences.
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
    return sorted(S) if unc == 0 else None


def _cover(k, m, rng, deadline):
    """Find S subset of Z_m, |S| = k, with S - S = Z_m, by annealing with restarts."""
    if m < k:
        return None
    if m == k:
        return list(range(m))
    while time.monotonic() < deadline:
        S = rng.sample(range(m), k)
        res = _anneal_cover(S, k, m, rng, deadline, iters=300000)
        if res is not None:
            return res
    return None


def _haar_climb(k, lo, deadline, rng):
    """Search m upward from lo for difference covers; return the largest (m, S) found, or None."""
    mmax = k * (k - 1) + 1
    best = None
    m = max(k, lo)
    fails = 0
    while m <= mmax and time.monotonic() < deadline:
        rem = deadline - time.monotonic()
        slice_end = time.monotonic() + max(1.0, 0.5 * rem)
        S = _cover(k, m, rng, min(deadline, slice_end))
        if S is not None:
            best = (m, S)
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                break
        m += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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
    budget = min(0.75 * float(time_limit), 42.0)
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

    if D >= 3:
        # Arc-extended projective plane graph (diameter 3, valid for D >= 3).
        arc = _arc_best(d, start + 0.3 * budget, random.Random(seed * 7919 + d))
        if arc is not None:
            consider(arc[0], arc[1])

    if D == 3 and d >= 2:
        # Haar graph from a difference cover: beats the arc graph iff 2m > best_n.
        lo = best_n // 2 + 1
        res = _haar_climb(d, lo, deadline, rng)
        if res is not None:
            m, S = res
            n, E = lib.haar_graph(m, S)
            consider(n, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
