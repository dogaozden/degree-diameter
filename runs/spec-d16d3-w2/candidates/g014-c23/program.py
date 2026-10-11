"""Pencil-attachment construction with independent side searches (D = 3).

Base: incidence graph of PG(2, q), with q the largest prime power such that
q + 1 <= d, so s = d - q - 1 spare degree remains on every vertex.

Extension: pick a set S_A of points and a set S_B of lines.
  - Each P in S_A gets a new side-0 vertex joined to the q+1 lines through P.
  - Each j in S_B gets a new side-1 vertex joined to the q+1 points on j.
Degree stays <= d exactly when every line lies on <= s points of S_A and every
point lies on <= s lines of S_B. Both are bounded-arc conditions, and they are
independent, so S_A and S_B can be searched separately. Diameter 3 holds for any
such sets, so the extension never needs a repair step.

Honest note on the target d = 16, D = 3: with q = 13 and s = 2, each side is a
set with at most 2 points per line, which is an arc of size at most q + 1 = 14.
That gives 366 + 28 = 394, the record. Within this family the cap is 394, so
this program is expected to reproduce the record and not exceed it. Covers that
could beat it would need non-pencil structure, which this program does not build.

Other D values: D = 2 uses a cycle or K_{d,d}; D >= 4 also tries the W(q)
generalized quadrangle. Every candidate is checked with lib.is_valid, and the
fallback is K_{d,d} (or C_{2D} for d = 2).
"""
import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base
# ----------------------------------------------------------------------------

def _pg(q):
    """PG(2,q) incidence. Points 0..m-1, lines indexed 0..m-1 (edge (u, m+L))."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]   # lines through point P
    line_points = [[] for _ in range(m)]   # points on line L
    for u, v in edges:
        L = v - m
        point_lines[u].append(L)
        line_points[L].append(u)
    return m, list(edges), point_lines, line_points


# ----------------------------------------------------------------------------
# Bounded sets: choose elements so that every resource is used at most s times.
# For S_A: element P uses resources point_lines[P] (lines), load <= s on lines.
# For S_B: element j uses resources line_points[j] (points), load <= s on points.
# ----------------------------------------------------------------------------

def _bounded_set(m, res, s, rng, deadline):
    rs = [set(r) for r in res]
    best = []
    first = True
    while first or time.monotonic() < deadline:
        first = False
        # Randomized greedy start.
        order = list(range(m))
        rng.shuffle(order)
        load = [0] * m
        S = set()
        for x in order:
            if all(load[r] < s for r in res[x]):
                S.add(x)
                for r in res[x]:
                    load[r] += 1
        if len(S) > len(best):
            best = sorted(S)
        # Plateau / swap local search.
        stall = 0
        while stall < 3000 and time.monotonic() < deadline:
            if len(S) > len(best):
                best = sorted(S)
            x = rng.randrange(m)
            if x in S:
                stall += 1
                continue
            sat = [r for r in res[x] if load[r] >= s]
            if not sat:
                S.add(x)
                for r in res[x]:
                    load[r] += 1
                stall = 0
                continue
            stall += 1
            rem = set()
            ok = True
            for r in sat:
                cands = [y for y in S if r in rs[y]]
                if not cands:
                    ok = False
                    break
                rem.add(rng.choice(cands))
                if len(rem) > 1:
                    ok = False
                    break
            if not ok or not rem:
                continue
            y = rem.pop()
            S.discard(y)
            for r in res[y]:
                load[r] -= 1
            if all(load[r] < s for r in res[x]):
                S.add(x)
                for r in res[x]:
                    load[r] += 1
            else:
                S.add(y)
                for r in res[y]:
                    load[r] += 1
    return best


def _assemble(m, edges, point_lines, line_points, SA, SB):
    """Plane incidence plus A-vertices (side 0, on lines through P) and B-vertices (side 1, on points of j)."""
    kA, kB = len(SA), len(SB)
    n = 2 * m + kA + kB
    E = list(edges)
    for t, P in enumerate(SA):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + kA + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the pencil-extended PG(2,q) graph."""
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        slot_end = now + (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, pl, lp = _pg(q)
        if s == 0:
            out.append((2 * m, edges))
            continue
        mid = now + (slot_end - now) / 2
        SA = _bounded_set(m, pl, s, rng, mid)
        SB = _bounded_set(m, lp, s, rng, slot_end)
        out.append(_assemble(m, edges, pl, lp, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (D = 4), as in the parent.
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
    rng = random.Random(seed * 1000003 + 31 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    fb_n, fb_E = lib.haar_graph(d, range(d))
    cands = []

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            cands.append(gq)

    if D >= 3:
        budget = 0.7 * time_limit if D == 3 else 0.2 * time_limit
        cands += _arc_candidates(d, start + budget, rng)

    cands.append((fb_n, fb_E))
    cands.sort(key=lambda t: -t[0])
    for n, E in cands:
        if lib.is_valid(n, E, d, D):
            return n, list(E)
    return fb_n, list(fb_E)
