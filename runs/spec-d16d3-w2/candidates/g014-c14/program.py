import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc construction (D = 3 fallback, from parent).
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
# New construction for D = 3: bi-Cayley (Haar-type) graph over Z_m.
#
# Vertices a_x and b_y (x, y in Z_m); a_x ~ b_y iff y - x in S, with |S| = d.
# The graph is d-regular and bipartite on 2m vertices. Same-side pairs are at
# distance <= 2 iff z - x lies in S - S, and cross-side pairs are at distance
# <= 3 whenever S - S covers Z_m. So we need a d-subset S of Z_m whose nonzero
# differences cover Z_m. Since |S - S \ {0}| <= d(d-1), this forces
# m <= d^2 - d + 1, which is exactly the Moore-type ceiling for D = 3.
# We search for such S by simulated annealing and grow m upward.
# ----------------------------------------------------------------------------

def _cyclic_cover(m, k, rng, deadline):
    """Find a k-subset S of Z_m with S - S covering all nonzero residues, or None."""
    if m < k:
        return None
    T = 0.4
    while time.monotonic() < deadline:
        S = rng.sample(range(m), k)
        inS = [False] * m
        for x in S:
            inS[x] = True
        cnt = [0] * m
        for a in S:
            for b in S:
                if a != b:
                    cnt[(a - b) % m] += 1
        unc = sum(1 for r in range(1, m) if cnt[r] == 0)
        best_unc = unc
        stall = 0
        while unc > 0:
            stall += 1
            if stall > 60000:
                break  # restart from a fresh random set
            if (stall & 1023) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(k)
            x = S[i]
            y = rng.randrange(m)
            if inS[y]:
                continue
            others = S[:i] + S[i + 1:]
            old = unc
            # Remove differences involving x.
            for t in others:
                r = (x - t) % m
                cnt[r] -= 1
                if cnt[r] == 0:
                    unc += 1
                r = (t - x) % m
                cnt[r] -= 1
                if cnt[r] == 0:
                    unc += 1
            # Add differences involving y.
            for t in others:
                r = (y - t) % m
                if cnt[r] == 0:
                    unc -= 1
                cnt[r] += 1
                r = (t - y) % m
                if cnt[r] == 0:
                    unc -= 1
                cnt[r] += 1
            dlt = unc - old
            if dlt <= 0 or rng.random() < math.exp(-dlt / T):
                S[i] = y
                inS[x] = False
                inS[y] = True
                if unc < best_unc:
                    best_unc = unc
                    stall = 0
            else:
                # Revert counts exactly, then restore the uncovered count.
                for t in others:
                    r = (y - t) % m
                    cnt[r] -= 1
                    r = (t - y) % m
                    cnt[r] -= 1
                for t in others:
                    r = (x - t) % m
                    cnt[r] += 1
                    r = (t - x) % m
                    cnt[r] += 1
                unc = old
        if unc == 0:
            return list(S)
    return None


def _bicayley_search(d, deadline, rng, consider):
    """Grow m upward from a fairly high start, emitting a valid 2m-vertex graph for each success."""
    mmax = d * d - d + 1
    m = max(d, int(0.7 * mmax))
    fails = 0
    while m <= mmax and time.monotonic() < deadline and fails < 2:
        rem = deadline - time.monotonic()
        sub = min(rem, max(4.0, 0.3 * rem))
        S = _cyclic_cover(m, d, rng, time.monotonic() + sub)
        if S is None:
            fails += 1
        else:
            fails = 0
            E = [(x, m + (x + s) % m) for x in range(m) for s in S]
            consider(2 * m, E)
        m += 1


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), from parent.
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
    budget = max(0.5, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed * 1000003 + d * 31 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D >= 3:
        cands = _arc_candidates(d, start + 0.15 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:3]:
            consider(n_c, E_c)

    if D == 3:
        _bicayley_search(d, deadline, rng, consider)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
