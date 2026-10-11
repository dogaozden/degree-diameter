import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (D = 3 fallback, the parent's construction)
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
# New construction for D = 3: bi-Cayley graphs over arbitrary small groups.
#
# For a finite group G of order M and a k-subset S of G, let the bipartite
# graph have parts A = G and B = G, with a_g ~ b_{g s} for s in S. It is
# k-regular. Distances are at most 3 whenever
#   (L) every x != e is of the form s t^{-1} (s != t in S), and
#   (R) every x != e is of the form s^{-1} t (s != t in S).
# Then A-A and B-B pairs are at distance <= 2, and mixed pairs at distance
# <= 3. Order = 2M, so the target is M >= 198 for d = 16 (beating 394).
# Nonabelian groups (Z_a x| Z_k) are searched alongside cyclic groups.
# ----------------------------------------------------------------------------

def _table(M, mul, inv):
    """Multiplication table and inverses for a group on 0..M-1 with identity 0."""
    mt = [[mul(x, y) for y in range(M)] for x in range(M)]
    iv = [inv(x) for x in range(M)]
    return M, mt, iv


def _group_options(m, rng):
    """Candidate groups of order m: the cyclic group plus up to two random semidirect products."""
    opts = []
    _, cmul, cinv = lib.cyclic_group(m)
    opts.append(_table(m, cmul, cinv))
    cands = []
    for k in range(2, m):
        if m % k != 0:
            continue
        a = m // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                cands.append((a, k, r))
    rng.shuffle(cands)
    for a, k, r in cands[:2]:
        order, mul, inv = lib.semidirect_group(a, k, r)
        opts.append(_table(order, mul, inv))
    return opts


def _anneal(M, mt, iv, k, rng, deadline):
    """Find a k-subset S of a group (0..M-1, identity 0) covering both quotient sets; or None."""
    if k * (k - 1) < M - 1:
        return None
    S = rng.sample(range(M), k)
    cL = [0] * M
    cR = [0] * M
    for a in S:
        for b in S:
            if a != b:
                cL[mt[a][iv[b]]] += 1
                cR[mt[iv[a]][b]] += 1
    unc = sum(1 for g in range(1, M) if cL[g] == 0) + sum(1 for g in range(1, M) if cR[g] == 0)
    inS = set(S)
    T = 1.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 200000 == 0:
            T = 0.6
        T = max(0.08, T * 0.99995)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(M)
        if y in inS:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        # Remove the ordered pairs involving x.
        for s in others:
            g = mt[x][iv[s]]
            cL[g] -= 1
            if cL[g] == 0:
                delta += 1
            g = mt[iv[x]][s]
            cR[g] -= 1
            if cR[g] == 0:
                delta += 1
            g = mt[s][iv[x]]
            cL[g] -= 1
            if cL[g] == 0:
                delta += 1
            g = mt[iv[s]][x]
            cR[g] -= 1
            if cR[g] == 0:
                delta += 1
        # Add the ordered pairs involving y.
        for s in others:
            g = mt[y][iv[s]]
            if cL[g] == 0:
                delta -= 1
            cL[g] += 1
            g = mt[iv[y]][s]
            if cR[g] == 0:
                delta -= 1
            cR[g] += 1
            g = mt[s][iv[y]]
            if cL[g] == 0:
                delta -= 1
            cL[g] += 1
            g = mt[iv[s]][y]
            if cR[g] == 0:
                delta -= 1
            cR[g] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS.discard(x)
            inS.add(y)
            unc += delta
        else:
            # Undo the addition, then the removal.
            for s in others:
                cL[mt[y][iv[s]]] -= 1
                cR[mt[iv[y]][s]] -= 1
                cL[mt[s][iv[y]]] -= 1
                cR[mt[iv[s]][y]] -= 1
            for s in others:
                cL[mt[x][iv[s]]] += 1
                cR[mt[iv[x]][s]] += 1
                cL[mt[s][iv[x]]] += 1
                cR[mt[iv[s]][x]] += 1
    return sorted(S)


def _bi_cayley(M, mt, S):
    """Bipartite graph on 2M vertices: a_g (vertex g) ~ b_{g s} (vertex M + mt[g][s]) for s in S."""
    edges = [(g, M + mt[g][s]) for g in range(M) for s in S]
    return 2 * M, edges


def _group_cover_search(k, rng, deadline):
    """Climb the group order m upward from a high start; keep the largest m with a cover found."""
    mmax = k * (k - 1) + 1
    m = max(k, int(0.8 * mmax))
    best = None
    fails = 0
    while m <= mmax and time.monotonic() < deadline:
        found = None
        remaining = deadline - time.monotonic()
        opts = _group_options(m, rng)
        per = max(0.4, remaining / (3.0 * len(opts)))
        for M, mt, iv in opts:
            now = time.monotonic()
            if now >= deadline:
                break
            S = _anneal(M, mt, iv, k, rng, min(deadline, now + per))
            if S is not None:
                found = (M, mt, S)
                break
        if found is not None:
            best = found
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
    budget = min(0.75 * float(time_limit), 42.0)
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
        # Secondary (safe): arc-extended projective plane, quick to build.
        cands = _arc_candidates(d, start + 0.2 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:1]:
            consider(n_c, E_c)
        # Primary (bold): bi-Cayley graphs over cyclic and nonabelian groups.
        if d >= 2:
            res = _group_cover_search(d, rng, start + 0.92 * budget)
            if res is not None:
                M, mt, S = res
                n, E = _bi_cayley(M, mt, S)
                consider(n, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
