import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (fallback for D = 3)
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
# Parent's cyclic difference-cover Haar search (D = 3 fallback)
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
    """Climb m upward from a high start, keeping the largest m with a difference cover. Returns (m, S) or None."""
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
# New bold construction for D = 3: Haar graphs over NON-abelian groups.
#
# For a group G of order m and a k-subset S of G, the bipartite graph with
# parts G x {A}, G x {B} and edges a_x ~ b_{xs} (s in S) is k-regular on 2m
# vertices. It has diameter <= 3 whenever S S^{-1} = G and S^{-1} S = G:
#   - A-A distance <= 2 needs every y^{-1}x in S S^{-1},
#   - B-B distance <= 2 needs S^{-1} S = G,
#   - mixed pairs then reach distance 3 since G S = G.
# The Moore-type cap is m <= k^2 - k + 1. Cyclic groups stall early, so we
# also search semidirect products Z_a x|_r Z_b, which include nonabelian groups.
# A simulated-annealing search over S minimises the number of uncovered elements.
# ----------------------------------------------------------------------------

def _groups_of_order(m, limit=8):
    """Candidate groups of order m as (order, mul, inv): cyclic plus some semidirect products."""
    out = [lib.cyclic_group(m)]
    for b in range(2, m + 1):
        if m % b:
            continue
        a = m // b
        if a < 2:
            continue
        cnt = 0
        for r in range(1, a):
            if math.gcd(r, a) != 1 or pow(r, b, a) != 1 % a:
                continue
            try:
                out.append(lib.semidirect_group(a, b, r))
            except ValueError:
                continue
            cnt += 1
            if cnt >= 3:
                break
        if len(out) >= limit:
            break
    return out[:limit]


def _anneal_cover(order, mul, inv, k, rng, deadline):
    """Find a k-subset S of the group with S S^-1 = G and S^-1 S = G. Returns sorted S or None."""
    tot = 2 * order
    cnt = [0] * tot
    unc = [tot]  # number of zero entries among the 2*order counters

    def idx(x, others):
        r = []
        ix = inv[x]
        for s in others:
            r.append(mul(x, inv[s]))           # x s^-1  (S S^-1 part)
            r.append(mul(s, ix))               # s x^-1
            r.append(order + mul(ix, s))       # x^-1 s  (S^-1 S part)
            r.append(order + mul(inv[s], x))   # s^-1 x
        r.append(0)            # x x^-1 = e
        r.append(order)        # x^-1 x = e (offset)
        return r

    def add(x, others):
        for g in idx(x, others):
            if cnt[g] == 0:
                unc[0] -= 1
            cnt[g] += 1

    def rem(x, others):
        for g in idx(x, others):
            cnt[g] -= 1
            if cnt[g] == 0:
                unc[0] += 1

    S = []
    for x in rng.sample(range(order), k):
        add(x, S)
        S.append(x)

    T = 0.6
    it = 0
    while unc[0] > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        x = S[i]
        others = S[:i] + S[i + 1:]
        y = rng.randrange(order)
        if y in S:
            continue
        before = unc[0]
        rem(x, others)
        add(y, others)
        delta = unc[0] - before
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
        else:
            rem(y, others)
            add(x, others)
    return sorted(S)


def _group_search(k, minm, maxm, rng, deadline):
    """Climb the group order m upward from minm; return (m, mul, S) for the largest success, or None."""
    best = None
    m = max(minm, k)
    while m <= maxm and time.monotonic() < deadline:
        groups = _groups_of_order(m)
        remaining = deadline - time.monotonic()
        slice_each = min(5.0, max(0.5, remaining / 4.0))
        found = None
        for order, mul, inv in groups:
            if time.monotonic() > deadline:
                break
            invt = [inv(x) for x in range(order)]
            S = _anneal_cover(order, mul, invt, k, rng,
                              min(deadline, time.monotonic() + slice_each))
            if S is not None:
                found = (order, mul, S)
                break
        if found is None:
            break
        best = (m, found[1], found[2])
        m += 1
    return best


def _group_haar_graph(m, mul, S):
    """Haar-type graph of a group: a_x ~ b_{x s} for s in S. Returns (2m, edges)."""
    edges = []
    for s in S:
        for x in range(m):
            edges.append((x, m + mul(x, s)))
    return 2 * m, edges


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
    budget = min(0.7 * float(time_limit), 40.0)
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
        # Parent's arc-extended projective plane (strong baseline).
        cands = _arc_candidates(d, start + 0.3 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:1]:
            consider(n_c, E_c)

        # Parent's cyclic difference-cover Haar graph (cheap secondary).
        res = _haar_search(d, rng, start + 0.35 * budget)
        if res is not None:
            m, S = res
            n, E = lib.haar_graph(m, S)
            consider(n, E)

        # Bold new step: Haar graphs over non-abelian groups, aiming above the record.
        minm = best_n // 2 + 1
        maxm = d * d - d + 1
        if minm <= maxm and time.monotonic() < deadline:
            gs = _group_search(d, minm, maxm, rng, deadline)
            if gs is not None:
                m, mul, S = gs
                n, E = _group_haar_graph(m, mul, S)
                consider(n, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
