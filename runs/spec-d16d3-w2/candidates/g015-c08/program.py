import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (D = 3 comparator)
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
    """For each prime power q with q + 1 <= d, build the arc-extended PG(2,q) graph."""
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
# Cyclic difference covers (parent's climbing search, kept as the baseline)
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
        for s in others:
            g = (y - s) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = (s - y) % m
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
                cnt[(y - s) % m] -= 1
                cnt[(s - y) % m] -= 1
            for s in others:
                cnt[(x - s) % m] += 1
                cnt[(s - x) % m] += 1
    return sorted(S)


def _haar_search(k, rng, deadline):
    """Climb m upward from a high start over cyclic groups. Returns (m, S) or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    m = max(k, int(0.8 * mmax))
    best = None
    fails = 0
    while m <= mmax and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        slice_ = max(0.5, remaining / 3.0)
        S = _cover_search(k, m, rng, min(deadline, time.monotonic() + slice_))
        if S is not None:
            best = (m, S)
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                break
        m += 1
    return best


# ----------------------------------------------------------------------------
# New construction for D = 3: Haar graphs over NON-ABELIAN groups.
#
# H(G, S) has parts A = G and B = G, with a_g ~ b_{gs} for s in S, |S| = k.
# It is k-regular and bipartite. Diameter <= 3 holds when both
#   S S^{-1} = G   (gives A-A and mixed distances)
#   S^{-1} S = G   (gives B-B distances)
# hold. In a nonabelian group these are two separate conditions, so the
# annealer tracks both at once. The order is 2|G| and |G| <= k(k-1)+1.
# We search over cyclic groups and semidirect products Z_a x| Z_b of each
# order, climbing upward from the cyclic baseline.
# ----------------------------------------------------------------------------

def _groups_of_order(M, rng, cap):
    """Semidirect products Z_a x| Z_b of order M (a*b = M, a >= 2, b >= 2), shuffled and capped."""
    out = []
    for b in range(2, M + 1):
        if M % b:
            continue
        a = M // b
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                out.append((a, b, r))
    rng.shuffle(out)
    return out[:cap]


def _tables(order, mul, inv):
    """Full multiplication table and inverse list for a group with elements 0..order-1 (identity 0)."""
    mt = [[mul(x, y) for y in range(order)] for x in range(order)]
    iv = [inv(x) for x in range(order)]
    return mt, iv


def _cover_group(m, mt, iv, k, rng, deadline):
    """Find S of size k in a group of order m with S S^{-1} = G and S^{-1} S = G, or None.

    cnt has 2m slots: slot g (1..m-1) counts ordered pairs (s,t), s != t, with s t^{-1} = g;
    slot m+g counts pairs with s^{-1} t = g. Slots 0 and m are never touched.
    """
    size = 2 * m
    while time.monotonic() < deadline:
        T = rng.choice((0.35, 0.5, 0.7))
        S = rng.sample(range(m), k)
        inS = [False] * m
        for s in S:
            inS[s] = True
        cnt = [0] * size
        for a in S:
            for b in S:
                if a != b:
                    cnt[mt[a][iv[b]]] += 1
                    cnt[m + mt[iv[a]][b]] += 1
        unc = sum(1 for i in range(size) if i != 0 and i != m and cnt[i] == 0)
        iters = 0
        limit = 80000
        while unc > 0 and iters < limit:
            iters += 1
            if (iters & 1023) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(k)
            x = S[i]
            y = rng.randrange(m)
            if inS[y]:
                continue
            others = S[:i] + S[i + 1:]
            delta = 0
            for s in others:
                for kk in (mt[x][iv[s]], m + mt[iv[x]][s], mt[s][iv[x]], m + mt[iv[s]][x]):
                    cnt[kk] -= 1
                    if cnt[kk] == 0:
                        delta += 1
            for s in others:
                for kk in (mt[y][iv[s]], m + mt[iv[y]][s], mt[s][iv[y]], m + mt[iv[s]][y]):
                    if cnt[kk] == 0:
                        delta -= 1
                    cnt[kk] += 1
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S[i] = y
                inS[x] = False
                inS[y] = True
                unc += delta
                if unc == 0:
                    return sorted(S)
            else:
                for s in others:
                    for kk in (mt[y][iv[s]], m + mt[iv[y]][s], mt[s][iv[y]], m + mt[iv[s]][y]):
                        cnt[kk] -= 1
                for s in others:
                    for kk in (mt[x][iv[s]], m + mt[iv[x]][s], mt[s][iv[x]], m + mt[iv[s]][x]):
                        cnt[kk] += 1
    return None


def _group_haar_edges(order, mt, S):
    """Edges of H(G, S): a_g = g joins b_{g s} = order + mt[g][s]."""
    return [(g, order + mt[g][s]) for g in range(order) for s in S]


def _group_climb(k, base_m, kmax, rng, deadline, consider):
    """For each order M from base_m+1 up to kmax, try the cyclic group and some semidirect products."""
    for M in range(max(base_m + 1, k), kmax + 1):
        if time.monotonic() > deadline:
            break
        cands = [("cyc",)] + [("sd",) + c for c in _groups_of_order(M, rng, 6)]
        for c in cands:
            now = time.monotonic()
            if now > deadline:
                return
            slice_end = min(deadline, now + 2.0)
            if c[0] == "cyc":
                mul = lambda x, y, M=M: (x + y) % M
                inv = lambda x, M=M: (-x) % M
                order = M
            else:
                a, b, r = c[1], c[2], c[3]
                order, mul, inv = lib.semidirect_group(a, b, r)
            mt, iv = _tables(order, mul, inv)
            S = _cover_group(order, mt, iv, k, rng, slice_end)
            if S is not None:
                consider(2 * order, _group_haar_edges(order, mt, S))
                break


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
        # Baseline: cyclic difference cover (parent's search), limited to 30% of budget.
        if d >= 2:
            res = _haar_search(d, rng, start + 0.3 * budget)
            if res is not None:
                m, S = res
                consider(*lib.haar_graph(m, S))
        # Bold change: climb through non-abelian Haar graphs above the cyclic baseline.
        if d >= 3:
            base_m = best_n // 2
            kmax = d * (d - 1) + 1
            _group_climb(d, base_m, kmax, rng, start + 0.85 * budget, consider)
        # Comparator: arc-extended projective plane (the parent's secondary construction).
        cands = _arc_candidates(d, start + 0.95 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c in cands[:1]:
            consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
