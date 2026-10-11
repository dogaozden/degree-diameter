import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane based candidates (diameter 3).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
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


def _arc_extensions(d, deadline, rng):
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
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
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
# Haar graphs from difference covers.
#
# H(Z_m, S) with |S| = d has a_i ~ b_{i+s}. If S - S = Z_m, every pair of
# same-side vertices is within distance 2 and every cross pair within 3, so
# the diameter is 3. Such S exists only when m <= d^2 - d + 1.
# The search anneals the number of uncovered differences to zero.
# ----------------------------------------------------------------------------

def _dec(cnt, a, others, m):
    """Remove element a from the set: decrement differences with others; return change in uncovered count."""
    delta = 0
    for t in others:
        for y in ((a - t) % m, (t - a) % m):
            cnt[y] -= 1
            if cnt[y] == 0:
                delta += 1
    return delta


def _inc(cnt, a, others, m):
    """Add element a to the set: increment differences with others; return change in uncovered count."""
    delta = 0
    for t in others:
        for y in ((a - t) % m, (t - a) % m):
            if cnt[y] == 0:
                delta -= 1
            cnt[y] += 1
    return delta


def _cover_search(d, m, rng, deadline):
    """Anneal a d-subset S of Z_m containing 0 with S - S = Z_m. Return S or None."""
    if m < d + 1 or m > d * d - d + 1:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    T = rng.choice([0.2, 0.35, 0.5])
    it = 0
    while unc > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[i]
        others = S[:i] + S[i + 1:]
        delta = _dec(cnt, old, others, m)
        delta += _inc(cnt, x, others, m)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
        else:
            _dec(cnt, x, others, m)
            _inc(cnt, old, others, m)
    return S


def _haar_search(d, D, rng, deadline, total, consider):
    """Search m downward from a high target until a cover is found, then upward while succeeding."""
    top = d * d - d + 1
    m = max(d + 1, min(top, int(0.83 * top)))
    won = None
    while time.monotonic() < deadline and d + 1 <= m <= top:
        rem = deadline - time.monotonic()
        cap = min(rem, max(1.0, 0.25 * total))
        S = _cover_search(d, m, rng, time.monotonic() + cap)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            consider(n, e)
            won = m if won is None else max(won, m)
            m += 1
        elif won is None:
            m -= 1
        else:
            break


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    deadline = start + total
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
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_extensions(d, start + 0.3 * total,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)
        _haar_search(d, D, rng, deadline, total, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
