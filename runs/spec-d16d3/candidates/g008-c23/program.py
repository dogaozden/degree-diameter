import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change for d=16, D=3: cyclic bipartite "Haar" graphs from difference
# covers instead of projective-plane extensions.
#
# Haar graph H(Z_m, S) with |S| = d: a_i ~ b_{i+s} for s in S. If the
# differences S - S cover all of Z_m, then every pair of A-vertices is at
# distance <= 2, every pair of B-vertices is at distance <= 2, and every
# A-B pair is at distance <= 3 (since S - S + S = Z_m). So diameter 3 holds
# and the order is 2m. For d=16 an order above 394 needs m >= 198, while the
# hard ceiling is m <= d(d-1)+1 = 241.
#
# Search: climb m upward from a comfortable start, and for each m run a
# local search that swaps one nonzero element of S and minimises the number
# of uncovered residues.
#
# Safety: K_{d,d} is always the fallback (diameter 2). The PG(2,q) arc
# extension (parent construction) and the W(q) quadrangle (D >= 4) remain
# as alternative candidates. Every candidate passes lib.is_valid before it
# is accepted.
# ----------------------------------------------------------------------------


def _apply(cnt, S, skip, v, sign, m):
    """Add (sign=+1) or remove (sign=-1) the differences between v and S[j], j != skip.

    Returns the change in the number of zero counts among residues 1..m-1.
    """
    dz = 0
    for j, s in enumerate(S):
        if j == skip:
            continue
        for r in ((v - s) % m, (s - v) % m):
            if sign > 0:
                if cnt[r] == 0:
                    dz -= 1
                cnt[r] += 1
            else:
                cnt[r] -= 1
                if cnt[r] == 0:
                    dz += 1
    return dz


def _cover_try(m, k, rng, deadline):
    """Find S subset of Z_m, |S| = k, 0 in S, with S - S covering Z_m. None on failure."""
    if m <= k or m > k * (k - 1) + 1:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for a in range(k):
        for b in range(k):
            if a != b:
                cnt[(S[a] - S[b]) % m] += 1
    zeros = sum(1 for r in range(1, m) if cnt[r] == 0)
    inS = set(S)
    T = 0.3
    steps = 0
    while zeros > 0:
        steps += 1
        if (steps & 511) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, k)
        x = S[i]
        while True:
            y = rng.randrange(1, m)
            if y not in inS:
                break
        old = zeros
        zeros += _apply(cnt, S, i, x, -1, m)
        zeros += _apply(cnt, S, i, y, 1, m)
        if zeros <= old or rng.random() < math.exp(-(zeros - old) / T):
            S[i] = y
            inS.discard(x)
            inS.add(y)
        else:
            zeros += _apply(cnt, S, i, y, -1, m)
            zeros += _apply(cnt, S, i, x, 1, m)
    return S


def _best_cover(k, deadline, rng):
    """Climb m upward while a difference cover of size k exists; return (m, S) for the largest found."""
    best = None
    m = max(k + 1, k * (k - 1) // 2 + 1)
    fails = 0
    while m <= k * (k - 1) + 1 and time.monotonic() < deadline:
        left = deadline - time.monotonic()
        S = _cover_try(m, k, rng, time.monotonic() + max(0.5, 0.3 * left))
        if S is not None:
            best = (m, S)
            m += 1
            fails = 0
        else:
            fails += 1
            if fails >= 4:
                break
    return best


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3, parent construction).
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


def _arc_candidates(d, deadline, rng):
    """Return (n, edges) candidates from arc extensions over prime powers q with q + 1 <= d."""
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
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4, parent construction).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.7 * time_limit, time_limit - 3.0)
    if budget < 0.5:
        budget = 0.5
    deadline = start + budget
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

    if D == 2:
        return best

    if D >= 3:
        # Main new construction: cyclic Haar graphs from difference covers.
        try:
            cover_deadline = start + 0.6 * budget
            cov = _best_cover(d, cover_deadline, random.Random(seed * 104729 + d))
            if cov is not None:
                m, S = cov
                n_h, e_h = lib.haar_graph(m, S)
                consider(n_h, e_h)
        except Exception:
            pass

        # Parent arc-extension candidates (diameter 3).
        try:
            for n_c, e_c in _arc_candidates(d, start + 0.85 * budget,
                                            random.Random(seed * 7919 + d)):
                if n_c > best_n:
                    consider(n_c, e_c)
        except Exception:
            pass

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
