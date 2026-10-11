import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound and projective-plane arc helpers (D = 3 arc-extension family)
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


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
# New construction for D = 3: multiplier-symmetric difference covers.
#
# The Haar graph H(m, S) (a_i ~ b_{i+s}, s in S, |S| = d) has diameter 3
# exactly when S - S = Z_m. Plain annealing over S is weak. The new helper
# restricts S to a union of orbits {x, ux, u^2 x, ...} under multiplication
# by a unit u of order r (r | d). Then S - S is closed under multiplication
# by u, the search space shrinks to C(m/r, d/r) choices, and the annealing
# converges much faster. Each orbit-union is checked for S - S = Z_m, and
# the search climbs m upward from about 0.8 * (d^2 - d + 1).
# ----------------------------------------------------------------------------

def _unit_of_order(m, r, rng, tries=400):
    """Return a unit u mod m of multiplicative order exactly r, or None."""
    if r == 1:
        return 1
    if m < 3:
        return None
    primes = [p for p in range(2, r + 1)
              if r % p == 0 and all(p % q for q in range(2, int(p ** 0.5) + 1))]
    one = 1 % m
    for _ in range(tries):
        u = rng.randrange(2, m)
        if math.gcd(u, m) != 1:
            continue
        if pow(u, r, m) != one:
            continue
        if all(pow(u, r // p, m) != one for p in primes):
            return u
    return None


def _orbits(m, u, r):
    """Full-size orbits of nonzero residues under multiplication by u (each of length r)."""
    seen = bytearray(m)
    orbs = []
    for x in range(1, m):
        if seen[x]:
            continue
        orb = []
        y = x
        for _ in range(r):
            orb.append(y)
            seen[y] = 1
            y = y * u % m
        if len(set(orb)) == r:
            orbs.append(orb)
    return orbs


def _orbit_cover_search(k, m, r, rng, deadline):
    """Find S, a union of k // r orbits under a unit of order r, with S - S = Z_m. Returns sorted S or None."""
    if r < 1 or k % r != 0:
        return None
    t = k // r
    if r == 1:
        orbs = [[x] for x in range(1, m)]
    else:
        u = _unit_of_order(m, r, rng)
        if u is None:
            return None
        orbs = _orbits(m, u, r)
    if len(orbs) < t:
        return None

    def cost(sel):
        S = [y for i in sel for y in orbs[i]]
        cov = set()
        for a in S:
            for b in S:
                if a != b:
                    cov.add((a - b) % m)
        return (m - 1) - len(cov), S

    sel = rng.sample(range(len(orbs)), t)
    c, S = cost(sel)
    T = 0.6
    stall = 0
    it = 0
    while c > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(t)
        j = rng.randrange(len(orbs))
        if j in sel:
            continue
        new = sel[:]
        new[i] = j
        c2, S2 = cost(new)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            sel, c, S = new, c2, S2
            stall = 0
        else:
            stall += 1
        if stall > 20000:
            sel = rng.sample(range(len(orbs)), t)
            c, S = cost(sel)
            stall = 0
    return sorted(set(S))


def _haar_search(k, rng, deadline):
    """Climb m upward from about 0.8 * mmax, trying orbit-symmetric covers. Returns (m, S) or None."""
    if k < 2:
        return None
    mmax = k * k - k + 1
    divs = [r for r in range(1, k + 1) if k % r == 0]
    m = max(k, int(0.8 * mmax))
    best = None
    fails = 0
    while m <= mmax and time.monotonic() < deadline:
        now = time.monotonic()
        m_deadline = min(deadline, now + max(1.0, min(8.0, deadline - now)))
        found = None
        order = divs[:]
        rng.shuffle(order)
        for idx, r in enumerate(order):
            now = time.monotonic()
            if now > m_deadline:
                break
            slice_end = now + (m_deadline - now) / (len(order) - idx)
            S = _orbit_cover_search(k, m, r, rng, slice_end)
            if S is not None and len(S) == k:
                found = S
                break
        if found is not None:
            best = (m, found)
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                break
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
    budget = min(0.75 * float(time_limit), 45.0)
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
        # Primary: orbit-symmetric Haar graph from a difference cover of size d in Z_m.
        if d >= 2:
            res = _haar_search(d, rng, start + 0.6 * budget)
            if res is not None:
                m, S = res
                n, E = lib.haar_graph(m, S)
                consider(n, E)
        # Secondary: arc-extended projective plane (conic/greedy arcs).
        cands = _arc_candidates(d, start + 0.85 * budget, random.Random(seed * 7919 + d))
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
