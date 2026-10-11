import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc extension (kept as a safe baseline for D = 3)
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
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
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
# New construction for D = 3: multiplicative-orbit difference covers.
#
# The Haar graph H(m, S) (a_i ~ b_{i+s}, s in S, |S| = k) is k-regular and has
# diameter 3 exactly when S - S = Z_m (a difference cover). The counting bound
# k(k-1) >= m - 1 caps m at k(k-1)+1.
#
# New idea: for prime m, pick a subgroup H of Z_m^* of order h (h | m-1) and
# force S to be a union of H-orbits (plus possibly the element 0). Then S - S
# is automatically H-invariant, so only orbit-level coverage matters. The
# search space shrinks from C(m, k) to C(m/h, t) orbit choices, and the
# annealing runs over orbit swaps. h = 1 recovers the unrestricted search.
# Candidates m are tried from the top down; a success raises the bar and
# removes the smaller m from consideration.
# ----------------------------------------------------------------------------

def _is_prime(n):
    """Trial-division primality test."""
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def _primitive_root(p):
    """Return a primitive root modulo the prime p."""
    if p == 2:
        return 1
    phi = p - 1
    fac = []
    x = phi
    f = 2
    while f * f <= x:
        if x % f == 0:
            fac.append(f)
            while x % f == 0:
                x //= f
        f += 1
    if x > 1:
        fac.append(x)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in fac):
            return g
    return None


def _subgroup(p, h):
    """Subgroup of Z_p^* of order h (h must divide p-1)."""
    g = _primitive_root(p)
    gen = pow(g, (p - 1) // h, p)
    H = set()
    x = 1
    for _ in range(h):
        H.add(x)
        x = x * gen % p
    return H


def _orbits(m, h):
    """Partition 1..m-1 into orbits of the order-h subgroup of Z_m^* (singletons when h = 1)."""
    H = _subgroup(m, h) if h > 1 else {1}
    seen = [False] * m
    orbs = []
    for x in range(1, m):
        if seen[x]:
            continue
        orb = sorted({x * u % m for u in H})
        for y in orb:
            seen[y] = True
        orbs.append(orb)
    return orbs


def _cover_cost(S, m):
    """Number of nonzero residues mod m that are not differences of two distinct elements of S."""
    diffs = set()
    for a in S:
        for b in S:
            if a != b:
                diffs.add((a - b) % m)
    return (m - 1) - len(diffs)


def _orbit_anneal(m, orbs, t, zero, rng, deadline):
    """Anneal over choices of t orbits (plus 0 if zero) until the set is a difference cover of Z_m."""
    N = len(orbs)

    def assemble(ch):
        S = [0] if zero else []
        for i in ch:
            S.extend(orbs[i])
        return S

    ch = rng.sample(range(N), t)
    cost = _cover_cost(assemble(ch), m)
    T = 0.5
    it = 0
    while cost > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(t)
        j = rng.randrange(N)
        if j in ch:
            continue
        new = ch[:]
        new[i] = j
        c = _cover_cost(assemble(new), m)
        if c <= cost or rng.random() < math.exp((cost - c) / T):
            ch = new
            cost = c
    return sorted(assemble(ch))


def _find_cover(k, lo, hi, rng, deadline):
    """Largest m in [lo, hi] for which a size-k difference cover of Z_m is found. Returns (m, S) or None."""
    attempts = []
    for m in range(hi, lo - 1, -1):
        if m < k:
            continue
        if _is_prime(m):
            hs = range(1, k + 1)
        else:
            hs = [1]
        for h in hs:
            if (m - 1) % h:
                continue
            for zero in (0, 1):
                if (k - zero) % h:
                    continue
                t = (k - zero) // h
                if t < 1 or (m - 1) // h < t:
                    continue
                attempts.append((m, h, zero, t))

    orbcache = {}
    best = None
    slice_ = 0.1
    while time.monotonic() < deadline:
        active = [a for a in attempts if best is None or a[0] > best[0]]
        if not active:
            break
        for (m, h, zero, t) in active:
            if best is not None and m <= best[0]:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            key = (m, h)
            if key not in orbcache:
                orbcache[key] = _orbits(m, h)
            S = _orbit_anneal(m, orbcache[key], t, zero, rng, min(deadline, now + slice_))
            if S is not None and (best is None or m > best[0]):
                best = (m, S)
        slice_ *= 2
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
    budget = min(0.7 * float(time_limit), 42.0)
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
        # Quick baseline: arc-extended projective plane (order 2(q^2+q+1) + 2(q+1) type).
        if d >= 2:
            cands = _arc_candidates(d, start + 0.15 * budget, random.Random(seed * 7919 + d))
            cands.sort(key=lambda t: -t[0])
            for n_c, E_c, _side in cands[:1]:
                consider(n_c, E_c)

        # Main: Haar graph from an orbit-invariant difference cover of size d.
        if d >= 2:
            k = d
            mmax = k * (k - 1) + 1
            lo = max(k, int(0.8 * mmax))
            res = _find_cover(k, lo, mmax, rng, start + 0.8 * budget)
            if res is None:
                res = _find_cover(k, k, lo - 1, rng, start + 0.9 * budget)
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
