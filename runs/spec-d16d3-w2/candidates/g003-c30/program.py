import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane helpers (baseline arc-extended PG(2,q) construction)
# ----------------------------------------------------------------------------

def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points and lines are both indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, pl, lp, S):
    """PG(2,q) incidence plus, per element of S, an A-vertex (joined to lines through it)
    and a B-vertex (joined to points on the line it indexes). Returns (n, edges, side)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in pl[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _prime_powers_desc(d):
    """Largest few prime powers q with q + 1 <= d (i.e. q <= d - 1)."""
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
    return qs[:3]


def _baseline_arc(d, q):
    """Arc-extended PG(2,q) using a conic when it fits the spare degree s = d - q - 1."""
    s = d - q - 1
    if s < 0:
        return None
    m, edges, pl, lp = _pg_incidence(q)
    S = []
    if s >= 2:
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cs = _conic_set(q, index)
        if _loads_ok(cs, s, m, pl, lp):
            S = cs
    if not _loads_ok(S, s, m, pl, lp):
        return None
    n, E, _side = _arc_graph(m, edges, pl, lp, S)
    return n, E


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4)
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
# Voltage-lift search over Z_m with a small base bipartite multigraph.
#
# Base: a vertices on side A and a on side B. Cell (i, j) carries M[i][j]
# distinct voltages in Z_m, row and column sums equal d. The lift has 2*a*m
# vertices. Since Z_m acts transitively on each fibre, diameter <= D holds iff
# every base vertex's radius-D ball covers the whole lift, so the cost is the
# total number of uncovered vertices from those 2a representatives.
# a = 1 is the Haar graph (difference-cover search).
# ----------------------------------------------------------------------------

def _lift_uncovered(n, nm, sources, D):
    total = 0
    for s in sources:
        ball = 1 << s
        for _ in range(D):
            nxt = ball
            x = ball
            while x:
                lb = x & -x
                nxt |= nm[lb.bit_length() - 1]
                x ^= lb
            if nxt == ball:
                break
            ball = nxt
        total += n - ball.bit_count()
    return total


def _lift_search(d, D, a, m, rng, deadline):
    """Simulated annealing over voltages. Returns (n, edges) on success, else None."""
    r = d % a
    base = d // a
    M = [[base + (1 if (j - i) % a < r else 0) for j in range(a)] for i in range(a)]
    volt = [[rng.sample(range(m), M[i][j]) for j in range(a)] for i in range(a)]
    n = 2 * a * m
    nm = [0] * n

    def flip(i, j, v, on):
        for g in range(m):
            A = i * m + g
            B = a * m + j * m + (g + v) % m
            if on:
                nm[A] |= 1 << B
                nm[B] |= 1 << A
            else:
                nm[A] &= ~(1 << B)
                nm[B] &= ~(1 << A)

    for i in range(a):
        for j in range(a):
            for v in volt[i][j]:
                flip(i, j, v, True)

    sources = [i * m for i in range(a)] + [a * m + j * m for j in range(a)]
    cost = _lift_uncovered(n, nm, sources, D)
    darts = [(i, j) for i in range(a) for j in range(a) if M[i][j] > 0]
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = (now - t0) / span
        T = 0.05 + 1.5 * (1.0 - frac)
        i, j = rng.choice(darts)
        k = rng.randrange(len(volt[i][j]))
        old = volt[i][j][k]
        cand = rng.randrange(m)
        if cand in volt[i][j]:
            continue
        flip(i, j, old, False)
        flip(i, j, cand, True)
        c2 = _lift_uncovered(n, nm, sources, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            volt[i][j][k] = cand
            cost = c2
        else:
            flip(i, j, cand, False)
            flip(i, j, old, True)

    E = []
    for i in range(a):
        for j in range(a):
            for v in volt[i][j]:
                for g in range(m):
                    E.append((i * m + g, a * m + j * m + (g + v) % m))
    return n, E


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * float(time_limit), 50.0)
    end = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    n0, E0 = lib.haar_graph(d, range(d))
    best = {"n": n0, "E": list(E0)}

    def consider(n, E):
        if n > best["n"] and lib.is_valid(n, E, d, D):
            best["n"] = n
            best["E"] = list(E)

    # Baseline constructions (instant).
    if D == 3:
        for q in _prime_powers_desc(d):
            res = _baseline_arc(d, q)
            if res is not None:
                consider(res[0], res[1])

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Search: voltage lifts with several base sizes. Larger a means smaller
    # group order needed, so each plan entry gets a share of the remaining time.
    nmax = lib.moore_bound(d, D)
    plan = [(2, 0.40), (3, 0.25), (4, 0.20), (1, 0.15)]
    search_end = start + 0.92 * budget
    total = max(0.0, search_end - time.monotonic())
    for a, frac in plan:
        if a > d:
            continue
        now = time.monotonic()
        if now >= search_end:
            break
        slice_end = min(search_end, now + frac * total)
        m = max(best["n"] // (2 * a) + 1, d // a + 1)
        while time.monotonic() < slice_end:
            if 2 * a * m > nmax:
                break
            res = _lift_search(d, D, a, m, rng, slice_end)
            if res is None:
                break
            n, E = res
            consider(n, E)
            m = max(m + 1, best["n"] // (2 * a) + 1)

    n_out, E_out = best["n"], best["E"]
    if not lib.is_valid(n_out, E_out, d, D):
        n_out, E_out = lib.haar_graph(d, range(d))
    return n_out, list(E_out)
