import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and arc extensions (diameter 3). This is the safe
# family: it reproduced the parent's record-level graph for d = 16.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _arc_extensions(d, deadline, rng, threshold):
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
# NEW FAMILY: cyclic Haar graphs via difference covering.
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, |S| = d. Two A-vertices are at
# distance 2 exactly when their difference lies in S - S, and paths between
# A-vertices have even length, so diameter <= 3 forces S - S to cover every
# nonzero residue of Z_m. This means m <= d(d-1)+1. A-B distances are then
# almost always <= 3; lib.is_valid confirms the final graph.
#
# We search for such an S by local search over the number of uncovered
# differences, and grow m while success keeps coming.
# ----------------------------------------------------------------------------

def _cover_search(m, d, rng, deadline):
    """Find S (|S| = d, 0 in S) in Z_m with S - S covering all nonzero residues; None on timeout."""
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)

    def swap(idx, new):
        """Replace S[idx] by new, updating difference counts and the uncovered count."""
        nonlocal unc
        old = S[idx]
        for j in range(d):
            if j == idx:
                continue
            t = S[j]
            for x in ((old - t) % m, (t - old) % m):
                cnt[x] -= 1
                if cnt[x] == 0:
                    unc += 1
            for x in ((new - t) % m, (t - new) % m):
                if cnt[x] == 0:
                    unc -= 1
                cnt[x] += 1
        S[idx] = new
        inS[old] = False
        inS[new] = True

    it = 0
    while unc > 0:
        it += 1
        if (it & 511) == 0 and time.monotonic() > deadline:
            return None
        idx = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if inS[new]:
            continue
        old = S[idx]
        before = unc
        swap(idx, new)
        if unc > before and rng.random() > 0.03:
            swap(idx, old)  # revert the move exactly
    return S


def _haar_search(d, best_n, consider, rng, deadline):
    """Grow the cyclic Haar graph: keep finding difference-covering S for m = best_n/2 + 1, ..."""
    m = best_n // 2 + 1
    while time.monotonic() < deadline:
        if m - 1 > d * (d - 1):
            break
        slice_end = min(deadline, time.monotonic() + 4.0)
        S = _cover_search(m, d, rng, slice_end)
        if S is None:
            continue  # retry the same m with a fresh random start
        n, e = lib.haar_graph(m, S)
        if consider(n, e):
            m = max(m, best_n // 2) + 1
        else:
            m += 1


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
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        arc_end = start + (0.3 if D == 3 else 0.6) * time_limit
        for n_c, e_c in _arc_extensions(d, arc_end, random.Random(seed * 7919 + d), best_n):
            consider(n_c, e_c)

    if D == 3:
        _haar_search(d, best_n, consider, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
