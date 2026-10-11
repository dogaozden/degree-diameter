import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (baseline for D = 3, the parent construction)
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
# New D = 3 construction: Haar-type graphs over NON-ABELIAN groups.
#
# For a finite group G of order N and a k-subset S of G, let H(G, S) have
# parts A = G and B = G with x_A ~ z_B iff z = x*s for some s in S.
# Its order is 2N and its degree is k.
#   * A-A distance <= 2  iff  every g in G lies in S S^{-1}.
#   * B-B distance <= 2  iff  every g in G lies in S^{-1} S.
#   * A-B distance <= 3  whenever S S^{-1} = G (then S S^{-1} S = G).
# So diameter 3 follows from S S^{-1} = G and S^{-1} S = G. Since
# |S S^{-1}| <= k(k-1)+1, we have N <= k(k-1)+1, giving the cap 2(k^2-k+1).
#
# Cyclic groups are a special case, but the search also uses semidirect
# products Z_m x| Z_k, which can cover larger orders. We run an annealing
# search on S for each candidate group, with ascending N so the best
# verified order is kept. Every result is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _make_group(spec):
    """Build (order, MUL, INV) for a group spec, or None if the inverse table is inconsistent."""
    kind, m, k, r = spec
    if kind == "cyc":
        order, mul, inv = lib.cyclic_group(m)
    else:
        order, mul, inv = lib.semidirect_group(m, k, r)
    MUL = [[mul(x, y) for y in range(order)] for x in range(order)]
    INV = [inv(x) for x in range(order)]
    for x in range(order):
        if MUL[x][INV[x]] != 0:
            return None
    return order, MUL, INV


def _specs(N, rng):
    """Candidate groups of order N: cyclic, plus semidirect products Z_m x| Z_k with m*k = N."""
    specs = [("cyc", N, 1, 0)]
    for k2 in range(2, N + 1):
        if N % k2:
            continue
        m = N // k2
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        nontriv = [r for r in rs if r != 1]
        rng.shuffle(nontriv)
        for r in nontriv[:3] + [1]:
            specs.append(("sd", m, k2, r))
    return specs


def _cover_group(MUL, INV, N, k, rng, deadline):
    """Annealing for S (|S| = k) with S S^{-1} = G and S^{-1} S = G. Returns sorted S or None."""
    cA = [0] * N
    cB = [0] * N
    S = rng.sample(range(N), k)
    inS = set(S)
    for s in S:
        for t in S:
            cA[MUL[s][INV[t]]] += 1
            cB[MUL[INV[s]][t]] += 1
    unc = sum(1 for g in range(N) if cA[g] == 0) + sum(1 for g in range(N) if cB[g] == 0)
    T = 0.5
    it = 0
    while unc > 0:
        it += 1
        if (it & 511) == 0 and time.monotonic() > deadline:
            return None
        if it % 200000 == 0:
            T = 0.5
        T = max(0.08, T * 0.99995)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(N)
        if y in inS:
            continue
        others = [S[j] for j in range(k) if j != i]
        rem = [(x, x)]
        add = [(y, y)]
        for t in others:
            rem.append((x, t))
            rem.append((t, x))
            add.append((y, t))
            add.append((t, y))
        delta = 0
        for s, t in rem:
            ga = MUL[s][INV[t]]
            gb = MUL[INV[s]][t]
            cA[ga] -= 1
            if cA[ga] == 0:
                delta += 1
            cB[gb] -= 1
            if cB[gb] == 0:
                delta += 1
        for s, t in add:
            ga = MUL[s][INV[t]]
            gb = MUL[INV[s]][t]
            if cA[ga] == 0:
                delta -= 1
            cA[ga] += 1
            if cB[gb] == 0:
                delta -= 1
            cB[gb] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS.discard(x)
            inS.add(y)
            unc += delta
        else:
            for s, t in add:
                cA[MUL[s][INV[t]]] -= 1
                cB[MUL[INV[s]][t]] -= 1
            for s, t in rem:
                cA[MUL[s][INV[t]]] += 1
                cB[MUL[INV[s]][t]] += 1
    return sorted(S)


def _group_search(lo, hi, k, rng, deadline):
    """Ascending search over orders N in [lo, hi]; returns (N, MUL, S) for the largest success."""
    best = None
    for N in range(lo, hi + 1):
        now = time.monotonic()
        if now >= deadline:
            break
        specs = _specs(N, rng)
        slice_N = (deadline - now) / (hi - N + 1)
        per = slice_N / max(1, len(specs))
        for spec in specs:
            t0 = time.monotonic()
            if t0 >= deadline:
                break
            G = _make_group(spec)
            if G is None:
                continue
            order, MUL, INV = G
            if order != N:
                continue
            S = _cover_group(MUL, INV, N, k, rng, min(deadline, t0 + per))
            if S is not None:
                best = (N, MUL, S)
                break
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

    if D == 3 and d >= 2:
        # Baseline: arc-extended projective plane (the parent construction).
        cands = _arc_candidates(d, start + 0.3 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c in [(c[0], c[1]) for c in cands[:1]]:
            consider(n_c, E_c)

        # Bold change: Haar-type graphs over groups of order N, aiming above the baseline.
        lo = best_n // 2 + 1
        hi = d * (d - 1) + 1
        if lo <= hi:
            res = _group_search(lo, hi, d, rng, start + 0.9 * budget)
            if res is not None:
                N, MUL, S = res
                E = [(x, N + MUL[x][s]) for x in range(N) for s in S]
                consider(2 * N, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
