import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc extension for D = 3 (parent construction, kept as a candidate)
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


# ----------------------------------------------------------------------------
# D = 3 via Haar graphs from difference covers.
#
# H(m, S): a_i ~ b_{i+s} for s in S, |S| = k. It has diameter 3 iff S - S = Z_m.
# Order 2m, degree k. Covers with k = 16 can exist for m up to 241 (the cap).
#
# New helper: targeted annealing. Most moves pick an uncovered difference g and
# insert y = s + g for some s in S, so the move covers g immediately. The rest
# are plain random swaps. Cost = number of uncovered nonzero residues.
# ----------------------------------------------------------------------------

def _cover_search(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m. Returns sorted S, or None."""
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
    if unc == 0:
        return sorted(S)
    T = 1.0
    it = 0
    while True:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 200000 == 0:
            T = 1.0  # reheat
        T = max(0.08, T * 0.99995)

        if rng.random() < 0.7:
            # Targeted move: cover an uncovered residue g by inserting s + g.
            g = rng.randrange(1, m)
            tries = 0
            while cnt[g] != 0 and tries < 40:
                g = rng.randrange(1, m)
                tries += 1
            if cnt[g] != 0:
                continue
            i = rng.randrange(k)
            s = S[i]
            y = (s + g) % m
            if y in in_s:
                continue
            j = rng.randrange(k - 1)
            if j >= i:
                j += 1
        else:
            j = rng.randrange(k)
            y = rng.randrange(m)
            if y in in_s:
                continue
        x = S[j]
        others = S[:j] + S[j + 1:]

        # Apply removal of x, then addition of y, tracking the change in uncovered count.
        delta = 0
        for s in others:
            for h in ((x - s) % m, (s - x) % m):
                cnt[h] -= 1
                if cnt[h] == 0:
                    delta += 1
        for s in others:
            for h in ((y - s) % m, (s - y) % m):
                if cnt[h] == 0:
                    delta -= 1
                cnt[h] += 1

        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[j] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
            if unc == 0:
                return sorted(S)
        else:
            # Revert: remove y's differences, restore x's.
            for s in others:
                for h in ((y - s) % m, (s - y) % m):
                    cnt[h] -= 1
            for s in others:
                for h in ((x - s) % m, (s - x) % m):
                    cnt[h] += 1


def _haar_sweep(k, rng, deadline):
    """Sweep m upward from 0.8*(k(k-1)+1); return the largest (m, S) found, or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    lo = max(k, int(0.8 * mmax))
    best = None
    m = lo
    while m <= mmax and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        slice_ = min(6.0, max(0.5, remaining / 4.0))
        S = _cover_search(k, m, rng, min(deadline, time.monotonic() + slice_))
        if S is not None:
            best = (m, S)
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
    budget = min(0.8 * float(time_limit), 48.0)
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
        # Arc-extended projective plane (parent construction), a quick candidate.
        cands = _arc_candidates(d, start + 0.3 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c in cands[:1]:
            consider(n_c, E_c)
        # Haar graph from a difference cover of size d, with targeted annealing.
        if d >= 2:
            res = _haar_sweep(d, rng, deadline - 0.5)
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
