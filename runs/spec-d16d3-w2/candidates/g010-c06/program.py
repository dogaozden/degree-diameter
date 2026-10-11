import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Moore bound and projective-plane arc helpers (D = 3 fallback)
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
# Haar graphs over finite abelian groups (D = 3).
#
# H(G, S): parts A = G and B = G, a_g ~ b_{g+s} for s in S, |S| = k.
# It is k-regular and bipartite. Same-side pairs are at distance <= 2 iff
# S - S = G (a "difference cover"), and mixed pairs are then within distance 3.
# The order is 2|G|. We search over the cyclic group Z_m and over the
# non-cyclic groups Z_a x Z_{m/a}, climbing m while covers are found.
# ----------------------------------------------------------------------------

def _group_ops(m, a):
    """Addition and negation tables for Z_a x Z_b (b = m // a); a = 1 gives the cyclic group Z_m."""
    idx = np.arange(m)
    if a == 1:
        add = (idx[:, None] + idx[None, :]) % m
        neg = (-idx) % m
    else:
        b = m // a
        X = idx // b
        Y = idx % b
        add = ((X[:, None] + X[None, :]) % a) * b + (Y[:, None] + Y[None, :]) % b
        neg = ((-X) % a) * b + (-Y) % b
    return add.astype(np.int64), neg.astype(np.int64)


def _anneal(m, Dl, k, rng, deadline):
    """Find S of size k in a group of order m with every non-identity element a difference of S.

    Dl[x][y] = x - y in the group (identity is element 0). Returns sorted S, or None on timeout.
    """
    S = rng.sample(range(m), k)
    in_s = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[Dl[a][b]] += 1
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
        Dx = Dl[x]
        Dy = Dl[y]
        delta = 0
        for s in others:
            g = Dx[s]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = Dl[s][x]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        for s in others:
            g = Dy[s]
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = Dl[s][y]
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
                cnt[Dy[s]] -= 1
                cnt[Dl[s][y]] -= 1
                cnt[Dx[s]] += 1
                cnt[Dl[s][x]] += 1
    return sorted(S)


def _haar_climb(k, m_start, rng, deadline):
    """Climb m upward from m_start. For each m try cyclic and a few non-cyclic groups; return (m, a, S) or None."""
    best = None
    m = max(k, m_start)
    mmax = k * (k - 1) + 1
    while m <= mmax and time.monotonic() < deadline:
        divs = [a for a in range(2, math.isqrt(m) + 1) if m % a == 0][:3]
        attempts = [1] + divs
        found = None
        for a in attempts:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            slice_ = max(1.0, remaining * 0.4)
            add, neg = _group_ops(m, a)
            Dt = add[np.arange(m)[:, None], neg[None, :]]
            Dl = Dt.tolist()
            S = _anneal(m, Dl, k, rng, min(deadline, time.monotonic() + slice_))
            if S is not None:
                found = (m, a, S)
                break
        if found is None:
            break
        best = found
        m += 1
    return best


def _haar_edges(m, a, S):
    """Edges of the Haar graph over Z_a x Z_{m/a}: a_g ~ b_{g+s}."""
    add, _ = _group_ops(m, a)
    addl = add.tolist()
    return [(g, m + addl[g][s]) for g in range(m) for s in S]


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
        # Primary: Haar graph over an abelian group with a difference cover of size d.
        # Start the climb near the Moore-type cap and go up as far as covers are found.
        if d >= 2:
            mmax = d * (d - 1) + 1
            m_start = max(d, int(0.8 * mmax))
            res = _haar_climb(d, m_start, rng, start + 0.7 * budget)
            if res is not None:
                m, a, S = res
                consider(2 * m, _haar_edges(m, a, S))
        # Secondary: arc-extended projective plane (guarantees the 394-vertex record for d = 16).
        cands = _arc_candidates(d, start + 0.92 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:1]:
            consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
