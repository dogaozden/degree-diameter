import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3), the parent's family.
# From PG(2, q) with spare s = d - q - 1, choose S with every line holding
# <= s points of S and every point on <= s lines indexed by S. Add an A-vertex
# per point of S and a B-vertex per line of S.
# ----------------------------------------------------------------------------

def _pg_data(q):
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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


def _arc_candidates(d, deadline, rng, threshold):
    """Arc-extended PG(2,q) graphs; q with a counting bound <= threshold are skipped."""
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
    qs.sort(reverse=True)

    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        qd = now + share
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = []
        g = _greedy_arc(m, s, pl, lp, rng, 40, now + 0.3 * share)
        if g:
            cands.append(g)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S0 = max(cands, key=len, default=[])
        if not _loads_ok(S0, s, m, pl, lp):
            S0 = []
        S = _local_arc(m, s, pl, lp, S0, rng, qd)
        if S and _loads_ok(S, s, m, pl, lp):
            out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# NEW FAMILY: cyclic Haar graphs H(m, S), |S| = d.
# Vertices a_i, b_j in Z_m; a_i ~ b_{i+s} for s in S. The graph is bipartite,
# d-regular on 2m vertices, and has diameter <= 3 exactly when S - S = Z_m
# (every residue is a difference of two elements of S, counting 0 via s - s).
# Search for S by local search that minimises the number of uncovered residues.
# ----------------------------------------------------------------------------

def _cover_set(d, m, rng, deadline):
    """Find S in Z_m with 0 in S, |S| = d, and S - S = Z_m; None on timeout."""
    cnt = [0] * m          # cnt[r] = number of ordered pairs (s, t), s != t, with s - t = r
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    for a in range(d):
        for b in range(d):
            if a != b:
                cnt[(S[a] - S[b]) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)

    def remove(x, others):
        nonlocal unc
        for s in others:
            for r in ((x - s) % m, (s - x) % m):
                cnt[r] -= 1
                if cnt[r] == 0:
                    unc += 1

    def add(x, others):
        nonlocal unc
        for s in others:
            for r in ((x - s) % m, (s - x) % m):
                if cnt[r] == 0:
                    unc -= 1
                cnt[r] += 1

    it = 0
    while unc > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, d)
        old = S[i]
        others = [S[j] for j in range(d) if j != i]
        x = rng.randrange(1, m)
        if inS[x]:
            continue
        before = unc
        remove(old, others)
        add(x, others)
        delta = unc - before
        if delta <= 0 or rng.random() < 0.03:
            inS[old] = False
            inS[x] = True
            S[i] = x
        else:
            remove(x, others)
            add(old, others)
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Parent's family first, so the result never drops below its value.
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_candidates(d, start + 0.2 * time_limit,
                                        random.Random(seed * 7919 + d), best_n):
            consider(n_c, e_c)

        # New family: cyclic Haar graphs with S - S = Z_m, looking for 2m > best_n.
        mmax = d * (d - 1) + 1
        m = max(best_n // 2 + 1, d)
        while m <= mmax and time.monotonic() < deadline:
            per_attempt = min(deadline, time.monotonic() + 2.0)
            S = _cover_set(d, m, rng, per_attempt)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
