import random
import time

import lib


# ----------------------------------------------------------------------------
# Two-sided arc extension of PG(2, q) incidence graphs (diameter 3).
#
# Base: point-line incidence graph of PG(2, q), points 0..m-1, lines m..2m-1,
# degree q+1. Spare capacity per old vertex: s = d - q - 1.
#
# Add new "A" vertices x_P (one per point P in SA), each joined to the q+1 lines
# through P, and new "B" vertices y_j (one per line j in SB), each joined to the
# q+1 points on j. Old lines gain load |SA ∩ L|, old points gain load
# #{j in SB : Q in j}; both must be <= s. SA and SB are chosen independently.
# Diameter stays 3 (checked by hand; lib.is_valid is the final gate).
#
# Each side is a set of elements with at most s on every incidence line/point,
# found by randomized greedy plus a plateau local search.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); lines are indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _conic(q, index):
    """Conic (plus nucleus for even q) as point indices; an arc in PG(2, q)."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _counts(S, inc, m):
    cnt = [0] * m
    for e in S:
        for x in inc[e]:
            cnt[x] += 1
    return cnt


def _fits(S, inc, m, s):
    return max(_counts(S, inc, m), default=0) <= s


def _greedy(m, inc, s, order):
    cnt = [0] * m
    S = []
    for e in order:
        if all(cnt[x] < s for x in inc[e]):
            S.append(e)
            for x in inc[e]:
                cnt[x] += 1
    return S


def _improve(S, m, inc, rev, s, rng, deadline):
    """Plateau local search: insert a random element, evict its conflicts, refill greedily."""
    cur = list(S)
    best = list(S)
    while time.monotonic() < deadline:
        inset = set(cur)
        cnt = _counts(cur, inc, m)
        e = rng.randrange(m)
        if e in inset:
            continue
        conflicts = set()
        for x in inc[e]:
            if cnt[x] >= s:
                for f in rev[x]:
                    if f in inset:
                        conflicts.add(f)
        new = [f for f in cur if f not in conflicts]
        cnt2 = _counts(new, inc, m)
        new.append(e)
        for x in inc[e]:
            cnt2[x] += 1
        in_new = set(new)
        pool = [f for f in range(m) if f not in in_new]
        rng.shuffle(pool)
        for f in pool:
            if all(cnt2[x] < s for x in inc[f]):
                new.append(f)
                for x in inc[f]:
                    cnt2[x] += 1
        if len(new) >= len(cur) or rng.random() < 0.05:
            cur = new
        if len(cur) > len(best):
            best = list(cur)
    return best


def _best_arc(m, inc, rev, s, rng, deadline, seed_set):
    init = seed_set if _fits(seed_set, inc, m, s) else []
    order = list(range(m))
    rng.shuffle(order)
    g = _greedy(m, inc, s, order)
    start = max([init, g], key=len)
    return _improve(start, m, inc, rev, s, rng, deadline)


def _assemble(m, edges, point_lines, line_points, SA, SB):
    E = list(edges)
    n = 2 * m
    for P in SA:
        x = n
        n += 1
        for L in point_lines[P]:
            E.append((x, m + L))
    for j in SB:
        y = n
        n += 1
        for Q in line_points[j]:
            E.append((Q, y))
    return n, E


def _candidate(q, d, rng, deadline):
    """Two-sided arc extension for PG(2, q) inside degree d; returns (n, edges)."""
    s = d - q - 1
    m, edges, point_lines, line_points = _pg(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    seed = _conic(q, index) if s >= 1 else []
    if s < 1:
        return _assemble(m, edges, point_lines, line_points, [], [])
    now = time.monotonic()
    half = max(0.0, (deadline - now) / 2)
    SA = _best_arc(m, point_lines, line_points, s, rng, now + half, seed)
    SB = _best_arc(m, line_points, point_lines, s, rng, now + 2 * half, seed)
    return _assemble(m, edges, point_lines, line_points, SA, SB)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.5 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    if D >= 3:
        qs = [q for q in range(2, min(d - 1, 23) + 1)
              if lib.is_prime_power(q) and q + 1 <= d]
        qs.sort(reverse=True)
        for idx, q in enumerate(qs):
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0:
                break
            slot = remaining / (len(qs) - idx)
            n, e = _candidate(q, d, rng, now + slot)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
