import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane baseline (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# From PG(2, q) incidence, with spare capacity s = d - q - 1 per vertex, pick a
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


def _local_improve(m, s, point_lines, line_points, S, rng, deadline, iters):
    """Plateau-walking 1-swap local search growing a feasible load-bounded set S."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m

    def add(P):
        inS[P] = True
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def rem(P):
        inS[P] = False
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fits(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    cur = list(S)
    for P in cur:
        add(P)
    best = list(cur)
    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            add(P)
            cur.append(P)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        R = cur[idx]
        rem(R)
        if fits(P):
            add(P)
            cur[idx] = P
        else:
            add(R)
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


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _local_improve(m, s, point_lines, line_points, g, rng, deadline, 3000)
            cands.append(g)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Bold family: Haar graphs with a difference cover.
#
# Haar graph H(m, S), |S| = k: a_i ~ b_j iff j - i in S. Each vertex has degree k.
# Facts (checked by reasoning, and re-checked by lib.is_valid before use):
#   * a_i to a_j is at distance 2 iff j - i in S - S, so S - S = Z_m suffices.
#   * a_0 to b_j: the walk a_0 - b_s - a_{s-t} - b_{s-t+u} reaches every j once
#     S - S = Z_m, so all cross pairs are within distance 3.
#   * H(m, S) has translations and a side-swap automorphism, so checking from a_0
#     covers every pair. Diameter is therefore at most 3.
# This gives order 2m with m up to k(k-1)+1, which exceeds the projective plane
# order for d=16 once m >= 198.
# ----------------------------------------------------------------------------

def _pair_update(cnt, m, v, others, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between v and each element of others.

    Returns the change in the number of residues r != 0 with cnt[r] == 0.
    """
    dz = 0
    for s in others:
        for r in ((v - s) % m, (s - v) % m):
            if sign < 0:
                cnt[r] -= 1
                if cnt[r] == 0:
                    dz += 1
            else:
                if cnt[r] == 0:
                    dz -= 1
                cnt[r] += 1
    return dz


def _haar_cover(m, k, rng, deadline):
    """Simulated-annealing search for S (0 in S, |S| = k) with S - S covering Z_m. None on failure."""
    if k < 2 or k > m:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)
    T = 0.4
    it = 0
    while unc:
        it += 1
        if (it & 127) == 0 and time.monotonic() >= deadline:
            return None
        i = rng.randrange(1, k)  # keep 0 fixed (translation invariance)
        x = S[i]
        y = rng.randrange(1, m)
        if inS[y]:
            continue
        others = S[:i] + S[i + 1:]
        dz = _pair_update(cnt, m, x, others, -1) + _pair_update(cnt, m, y, others, +1)
        if dz <= 0 or rng.random() < math.exp(-dz / T):
            unc += dz
            S[i] = y
            inS[x] = False
            inS[y] = True
        else:
            _pair_update(cnt, m, y, others, -1)
            _pair_update(cnt, m, x, others, +1)
    return S


def _haar_search(d, lo, hi, rng, deadline, per_try, tries, consider):
    """Ascending search over m in [lo, hi]; stops after 3 consecutive failed m values."""
    fails = 0
    m = lo
    while m <= hi and fails < 3 and time.monotonic() < deadline:
        S = None
        for _ in range(tries):
            if time.monotonic() >= deadline:
                break
            tdl = min(deadline, time.monotonic() + per_try)
            S = _haar_cover(m, d, rng, tdl)
            if S is not None:
                break
        if S is None:
            fails += 1
        else:
            fails = 0
            consider(*lib.haar_graph(m, S))
        m += 1


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        # Projective-plane baseline, then arc extension (fast, reaches 394 for d=16).
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_extensions(d, start + 0.2 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

        # Bold family: Haar graphs with a difference cover, searching upward from
        # the current record half-order.
        if d >= 2:
            lo = max(d, best[0] // 2 + 1)
            hi = d * (d - 1) + 1
            _haar_search(d, lo, hi, rng, deadline, 0.06 * time_limit, 3, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
