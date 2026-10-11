"""Bold variant: single-orbit bi-Cayley lifts over semidirect products.

For D >= 3 the main search replaces the parent's multi-layer voltage annealing with
one family. The graph has parts A = G and B = G and edges a_g ~ b_{g*s} for a set S of
d distinct group elements, where G = Z_a x| Z_b (cyclic when b = 1, possibly
nonabelian). Left multiplication by G is an automorphism, so the graph is
vertex-transitive on each side. Validity therefore reduces to two BFS runs, from a_e
and b_e, counting unreached vertices. The search is simulated annealing over S, and
the group order M is climbed upward from the best valid graph found so far. Baseline
algebraic constructions and K_{d,d} are kept as fallbacks, and every output is checked
with lib.is_valid.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines (projective plane, Araujo-Pardo-Lopez, arc extensions, GQ).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
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
# Single-orbit bi-Cayley lifts over groups of order M.
# ----------------------------------------------------------------------------

def _group_options(M):
    """Semidirect presentations (a, b, r) of groups of order M: Z_M, plus Z_a x| Z_b with a*b = M."""
    opts = [(M, 1, 1)]
    for b in range(2, M + 1):
        if M % b:
            continue
        a = M // b
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                opts.append((a, b, r))
    return opts


def _reach_unreached(Rs, Ls, M, D, src_is_A):
    """Vertices (both sides) not within distance D of the identity on the source side.

    Rs[t][g] = g*s_t (A -> B), Ls[t][h] = h*s_t^{-1} (B -> A).
    """
    visA = np.zeros(M, dtype=bool)
    visB = np.zeros(M, dtype=bool)
    front = np.array([0], dtype=np.int64)
    if src_is_A:
        visA[0] = True
        on_a = True
    else:
        visB[0] = True
        on_a = False
    for _ in range(D):
        nb = np.zeros(M, dtype=bool)
        if on_a:
            for R in Rs:
                nb[R[front]] = True
            nb &= ~visB
            visB |= nb
        else:
            for L in Ls:
                nb[L[front]] = True
            nb &= ~visA
            visA |= nb
        front = np.flatnonzero(nb)
        on_a = not on_a
        if front.size == 0:
            break
    return 2 * M - int(visA.sum()) - int(visB.sum())


def _search_group(d, D, M, mul, inv, rng, deadline, iters):
    """Anneal a d-set S of group elements so the bi-Cayley graph has diameter <= D. Returns S or None."""
    if M < d:
        return None
    cache = {}

    def get(s):
        if s not in cache:
            R = np.fromiter((mul(g, s) for g in range(M)), dtype=np.int64, count=M)
            si = inv(s)
            L = np.fromiter((mul(h, si) for h in range(M)), dtype=np.int64, count=M)
            cache[s] = (R, L)
        return cache[s]

    def cost(S):
        ps = [get(s) for s in S]
        Rs = [p[0] for p in ps]
        Ls = [p[1] for p in ps]
        return _reach_unreached(Rs, Ls, M, D, True) + _reach_unreached(Rs, Ls, M, D, False)

    S = rng.sample(range(M), d)
    c = cost(S)
    T = 2.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(M)
        if x in S:
            continue
        S2 = list(S)
        S2[i] = x
        c2 = cost(S2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / max(T, 1e-3)):
            S, c = S2, c2
        T = max(0.3, T * 0.999)
    return S if c == 0 else None


def _lift_edges(M, S, mul):
    """Edges a_g -- b_{g*s} for s in S, with A = 0..M-1 and B = M..2M-1."""
    E = []
    for s in S:
        for g in range(M):
            E.append((g, M + mul(g, s)))
    return E


# ----------------------------------------------------------------------------

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
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
        for n_c, e_c in _arc_extensions(d, start + 0.1 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # A graph already at the Moore bound cannot be beaten.
    if best_n >= target:
        return best

    # Main search: climb the group order M just above the current best.
    while time.monotonic() < deadline:
        base = best_n // 2
        W = max(2, base // 12)
        M = max(d, base + rng.randint(1, W))
        opts = _group_options(M)
        a, b, r = rng.choice(opts)
        order, mul, inv = lib.semidirect_group(a, b, r)
        attempt_end = min(deadline, time.monotonic() + 2.5)
        S = _search_group(d, D, order, mul, inv, rng, attempt_end, 6000)
        if S is not None:
            e = _lift_edges(order, S, mul)
            consider(2 * order, e)
            if best_n >= target:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
