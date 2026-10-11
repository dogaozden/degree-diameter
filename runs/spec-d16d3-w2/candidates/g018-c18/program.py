import itertools
import math
import random
import time

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
# H(m, S): parts Z_m and Z_m, a_i ~ b_{i+s} for s in S. It is |S|-regular and
# bipartite. Diameter <= 3 holds when S - S = Z_m (a difference cover).
#
# NEW HELPER: directed cover search. Instead of random swaps, each move picks an
# UNCOVERED difference g and places a new element y = s +- g next to an existing
# element s, so the move is guaranteed to create the missing difference. Accepted
# with simulated-annealing rule on the number of uncovered differences.
# ----------------------------------------------------------------------------

def _remove_contrib(cnt, x, others, m):
    """Remove element x's ordered differences against `others`; return change in uncovered count."""
    delta = 0
    for s in others:
        g = (x - s) % m
        cnt[g] -= 1
        if cnt[g] == 0:
            delta += 1
        g = (s - x) % m
        cnt[g] -= 1
        if cnt[g] == 0:
            delta += 1
    return delta


def _add_contrib(cnt, y, others, m):
    """Add element y's ordered differences against `others`; return change in uncovered count."""
    delta = 0
    for s in others:
        g = (y - s) % m
        if cnt[g] == 0:
            delta -= 1
        cnt[g] += 1
        g = (s - y) % m
        if cnt[g] == 0:
            delta -= 1
        cnt[g] += 1
    return delta


def _pick_uncovered(cnt, m, rng):
    """Return a uniformly-ish random g in 1..m-1 with cnt[g] == 0, or None if none exists."""
    for _ in range(40):
        g = rng.randrange(1, m)
        if cnt[g] == 0:
            return g
    zeros = [g for g in range(1, m) if cnt[g] == 0]
    return rng.choice(zeros) if zeros else None


def _directed_cover(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m using directed moves. Returns sorted S or None."""
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
    T = 0.8
    it = 0
    while unc > 0:
        it += 1
        if (it & 511) == 0:
            if time.monotonic() > deadline:
                return None
        if it % 200000 == 0:
            T = 0.8  # reheat to escape stagnation
        T = max(0.12, T * 0.99993)

        g = _pick_uncovered(cnt, m, rng)
        if g is None:
            break
        i = rng.randrange(k)
        x = S[i]
        others = S[:i] + S[i + 1:]
        s = rng.choice(others)
        y = (s + g) % m if rng.random() < 0.5 else (s - g) % m
        if y in in_s:
            continue

        delta = _remove_contrib(cnt, x, others, m)
        delta += _add_contrib(cnt, y, others, m)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            # Roll back: undo y, then restore x.
            _remove_contrib(cnt, y, others, m)
            _add_contrib(cnt, x, others, m)
    return sorted(S)


def _haar_search(k, m_start, rng, deadline):
    """Climb m upward from m_start while difference covers are found. Returns (m, S) or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    m = max(k, m_start)
    best = None
    first = True
    while m <= mmax:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        slice_ = remaining * (0.6 if first else 0.5)
        S = _directed_cover(k, m, rng, time.monotonic() + slice_)
        if S is None:
            break
        best = (m, S)
        first = False
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
        # Arc-extended projective plane (quick, gives a strong baseline).
        arcs = _arc_candidates(d, start + 0.2 * budget, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        if arcs:
            consider(arcs[0][0], arcs[0][1])

        # Haar graph from a difference cover, searching only orders that beat the baseline.
        if d >= 2:
            m_start = max(d, best_n // 2 + 1)
            res = _haar_search(d, m_start, rng, deadline)
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
