import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane baseline (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
#
# From PG(2, q) incidence with spare capacity s = d - q - 1 per vertex, choose a
# point set S with every line holding <= s points of S and every point on <= s
# lines of S. Add an A-vertex per point of S and a B-vertex per line of S.
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


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large feasible S, starting from S0."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in point_lines[P] if cl[L] >= s}
        satQ = {Q for Q in line_points[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in point_lines[R])
                or any(Q in satQ for Q in line_points[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
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


def _arc_extensions(d, deadline, rng, threshold):
    """Return a list of (n, edges) candidates from arc extensions of PG(2, q)."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        kmax = s * m // (q + 1)
        if 2 * m + 2 * kmax <= threshold:
            continue
        qs.append((q, s))

    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        q_deadline = now + share
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, now + 0.3 * share)]
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S0 = max(cands, key=len, default=[])
        if not _loads_ok(S0, s, m, point_lines, line_points):
            S0 = []
        S = _local_arc(m, s, point_lines, line_points, S0, rng, q_deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Group Haar graphs (new bold family for D = 3).
#
# Over a finite group G of order m with a set S of size d (containing the
# identity), let a_g ~ b_{g s} for s in S. This is bipartite, d-regular on
# 2m vertices. Distances: a-a and b-b pairs at distance <= 2 exactly when
# S S^{-1} = G and S^{-1} S = G; then every a-b pair is within distance 3.
# So diameter 3 holds iff both covering conditions hold. Since |S S^{-1}| <= d^2 - d + 1,
# we have m <= d(d-1)+1, i.e. 2m <= 482 for d = 16.
# We search for S by simulated annealing on the number of uncovered elements.
# ----------------------------------------------------------------------------

def _group_tables_for(m, rng, cap=8):
    """Multiplication and inverse tables for several groups of order m (cyclic and semidirect)."""
    specs = [(m, 1, 1)]  # cyclic Z_m
    for b in range(2, m):
        if m % b:
            continue
        a = m // b
        if a < 2:
            continue
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
        if rs:
            specs.append((a, b, rng.choice(rs)))
            if len(rs) > 1:
                specs.append((a, b, rng.choice(rs)))
    rng.shuffle(specs)
    tables = []
    for a, b, r in specs[:cap]:
        try:
            order, mul, inv = lib.semidirect_group(a, b, r)
        except ValueError:
            continue
        if order != m:
            continue
        MUL = [[mul(x, y) for y in range(m)] for x in range(m)]
        IV = [inv(x) for x in range(m)]
        tables.append((MUL, IV))
    return tables


def _climb(m, d, MUL, IV, rng, iters, deadline):
    """Anneal S (size d, containing identity 0) so that S S^{-1} = G = S^{-1} S."""
    def cost(S):
        P1 = {MUL[s][IV[t]] for s in S for t in S}
        P2 = {MUL[IV[s]][t] for s in S for t in S}
        return 2 * m - len(P1) - len(P2)

    S = [0] + rng.sample(range(1, m), d - 1)
    c = cost(S)
    for it in range(iters):
        if c == 0:
            return S
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = cost(T)
        temp = 0.6 * (1 - it / iters) + 0.02
        if ct <= c or rng.random() < math.exp(-(ct - c) / temp):
            S, c = T, ct
    return S if c == 0 else None


def _haar_search(m, d, deadline, rng, tables):
    """Try random restarts over the given group tables until deadline; return (n, edges) or None."""
    while time.monotonic() < deadline:
        MUL, IV = tables[rng.randrange(len(tables))]
        S = _climb(m, d, MUL, IV, rng, 15000, min(deadline, time.monotonic() + 2.0))
        if S is not None:
            edges = [(g, m + MUL[g][s]) for g in range(m) for s in S]
            return 2 * m, edges
    return None


def _haar_ladder(d, deadline, rng):
    """Climb the order m upward from near the bound, returning the largest success."""
    M = d * (d - 1) + 1
    best = None
    target = max(d, int(0.85 * M))
    while time.monotonic() < deadline and d <= target <= M:
        tables = _group_tables_for(target, rng)
        if not tables:
            target -= 1
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res = _haar_search(target, d, slice_end, rng, tables)
        if res is not None:
            best = res
            target += 1
        elif best is None:
            target -= 2
            if target < d:
                break
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Arc-extended projective plane graphs: a known-good family, kept as a fallback.
        for n_c, e_c in _arc_extensions(d, start + 0.4 * time_limit,
                                        random.Random(seed * 7919 + d), best_n):
            consider(n_c, e_c)

        # Bold family: group Haar graphs with S S^{-1} = G = S^{-1} S, diameter 3.
        res = _haar_ladder(d, start + 0.85 * time_limit, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
