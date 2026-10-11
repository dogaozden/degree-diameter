import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family 1: projective plane incidence graph (diameter 3, degree q + 1).
# ----------------------------------------------------------------------------

def _pg_graph(d):
    """Return (n, edges) of PG(2, q) incidence for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Family 2: PG(2, q) plus A/B vertices over a conic (hyperoval for even q).
# Needs spare degree >= 2, i.e. q + 3 <= d. Every line holds <= 2 points of S
# and every point lies on <= 2 lines of S, so degrees stay <= q + 3.
# ----------------------------------------------------------------------------

def _arc_graph(q):
    """Return (n, edges) for PG(2,q) plus one A vertex per point of S and one B vertex per line of S."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    m = len(pts)
    _, edges = lib.projective_plane_incidence(q)
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)

    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
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


# ----------------------------------------------------------------------------
# Family 3 (bold, new): Haar graphs H(Z_m, S) with |S| = d and S - S = Z_m.
#
# A Haar graph is bipartite and d-regular on 2m vertices. Same-side distances
# are even, so they are <= 2 exactly when S - S covers Z_m. Cross-side pairs
# then have distance <= 3, because S - S + S = Z_m. Hence any difference cover
# S of Z_m with |S| = d gives a valid diameter-3 graph on 2m vertices. For
# d = 16 the Moore bound is 2 * 241, so m may range over [198, 241], and
# m >= 198 beats the 394 record. We search for covers by simulated annealing.
# ----------------------------------------------------------------------------

def _update(cnt, m, others, x, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between x and the elements of others.

    Returns the change in the number of uncovered residues.
    """
    change = 0
    for y in others:
        for dd in ((x - y) % m, (y - x) % m):
            if sign > 0:
                if cnt[dd] == 0:
                    change -= 1
                cnt[dd] += 1
            else:
                cnt[dd] -= 1
                if cnt[dd] == 0:
                    change += 1
    return change


def _diff_cover(m, k, rng, deadline):
    """Find S in Z_m with 0 in S, |S| = k, and S - S = Z_m. Returns the list S, or None on timeout."""
    if k > m or k * (k - 1) < m - 1:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = [False] * m
    for x in S:
        inS[x] = True
    cnt = [0] * m
    for x in S:
        for y in S:
            if x != y:
                cnt[(x - y) % m] += 1
    uncovered = sum(1 for r in range(1, m) if cnt[r] == 0)
    T = 0.35
    it = 0
    while uncovered > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, k)
        old = S[i]
        others = [y for y in S if y != old]
        if rng.random() < 0.85:
            unc = [r for r in range(1, m) if cnt[r] == 0]
            r = rng.choice(unc)
            new = (rng.choice(others) + r) % m
        else:
            new = rng.randrange(1, m)
        if new == 0 or inS[new]:
            continue
        ch = _update(cnt, m, others, old, -1)
        ch += _update(cnt, m, others, new, +1)
        if ch <= 0 or rng.random() < math.exp(-ch / T):
            S[i] = new
            inS[old] = False
            inS[new] = True
            uncovered += ch
        else:
            _update(cnt, m, others, new, -1)
            _update(cnt, m, others, old, +1)
    return S


def _haar_search(d, D, best_n, rng, deadline, per_m):
    """Sweep m upward from the current best order / 2 + 1; return the largest valid Haar graph found, or None."""
    lo = best_n // 2 + 1
    hi = d * d - d + 1  # Moore bound 2(d^2 - d + 1) for bipartite diameter 3
    result = None
    m = lo
    while m <= hi and time.monotonic() < deadline:
        end = min(deadline, time.monotonic() + per_m)
        S = _diff_cover(m, d, rng, end)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            if lib.is_valid(n, e, d, D):
                result = (n, e)
        m += 1
    return result


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.3, min(0.8 * time_limit, time_limit - 3.0))
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
        pg = _pg_graph(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Conic arc family: needs q + 3 <= d.
        for q in range(2, d - 2):
            if lib.is_prime_power(q):
                try:
                    n_c, e_c = _arc_graph(q)
                    consider(n_c, e_c)
                except Exception:
                    pass

        # Bold family: Haar graphs from difference covers, searched above the current best.
        if time.monotonic() < deadline:
            try:
                h = _haar_search(d, D, best_n, rng, deadline, per_m=3.5)
                if h is not None:
                    consider(h[0], h[1])
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
