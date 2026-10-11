import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change for d = q + 3 (here d = 16, q = 13): "mixed pencil" graphs.
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Old vertices
# have degree q+1, so spare capacity is s = d - q - 1 = 2.
#
# Let Bset be a dual arc of q+1 lines (no three concurrent), taken as the dual
# conic. Every point then lies on at most 2 lines of Bset. Let D2 be the points
# lying on exactly 2 lines of Bset.
#
# For each chosen point P in SA (a subset of D2), add a new A-vertex joined to
# the q+1-2 lines through P that are not in Bset, and to the 2 new B-vertices of
# the two Bset lines through P. For each line M in Bset, add one new B-vertex
# joined to the q+1 points of M.
#
# Capacity: an old line L not in Bset gains one edge per A-vertex, so we need
# at most 2 SA points on each non-Bset line. An old point gains one edge per
# B-vertex, at most 2. Every new vertex has degree q+1 <= d.
#
# Diameter 3 holds: A-vertices reach every old point within 2 (through a line
# or a B-vertex), A-A pairs always share a common neighbour, and all other pairs
# are within 3. Order = 2(q^2+q+1) + |SA| + (q+1). The record 394 needs
# |SA| >= 15; this is found by local search over D2. The result is always
# checked by lib.is_valid, with the parent-style arc graph or K_{d,d} as fallback.
#
# Only d = q + 3 uses this family. For other cases the program falls back to
# the arc-extended graph or K_{d,d}. Those are valid for D >= 3 and D >= 2.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _conic(q, index):
    """Conic (plus nucleus for even q) as a point index list; the same indices name lines."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(q, d):
    """Parent-style arc extension of PG(2, q) with s = d - q - 1 spare capacity."""
    m, edges, point_lines, line_points, index = _pg(q)
    s = d - q - 1
    S = _conic(q, index) if s >= 2 else []
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        for L in point_lines[P]:
            E.append((2 * m + t, m + L))
    for t, j in enumerate(S):
        for Q in line_points[j]:
            E.append((Q, 2 * m + k + t))
    return n, E


def _mixed(q, d, deadline, rng):
    """Mixed-pencil graph for d = q + 3. Returns (n, edges) or None."""
    if d != q + 3:
        return None
    m, edges, point_lines, line_points, index = _pg(q)
    Bl = _conic(q, index)
    Bset = set(Bl)
    bload = [0] * m
    for L in Bl:
        for Q in line_points[L]:
            bload[Q] += 1
    if max(bload) > 2:
        return None
    D2 = [P for P in range(m) if bload[P] == 2]
    if not D2:
        return None
    nb = {P: [L for L in point_lines[P] if L not in Bset] for P in D2}

    # Local search: maximise |SA| subject to <= 2 SA points on each non-Bset line.
    cnt = [0] * m
    cur = set()
    order = D2[:]
    rng.shuffle(order)
    for P in order:
        if all(cnt[L] < 2 for L in nb[P]):
            cur.add(P)
            for L in nb[P]:
                cnt[L] += 1
    best = set(cur)
    while time.monotonic() < deadline:
        c = rng.choice(D2)
        if c in cur:
            continue
        removed = []
        for L in nb[c]:
            while cnt[L] >= 2:
                opts = [R for R in line_points[L] if R in cur]
                R = rng.choice(opts)
                cur.discard(R)
                removed.append(R)
                for M in nb[R]:
                    cnt[M] -= 1
        if len(removed) >= 2 and rng.random() > 0.03:
            # Reject a net loss (rarely accept to escape plateaus).
            for R in removed:
                cur.add(R)
                for M in nb[R]:
                    cnt[M] += 1
            continue
        cur.add(c)
        for L in nb[c]:
            cnt[L] += 1
        if len(cur) > len(best):
            best = set(cur)

    # Build the graph from the best SA set.
    SA = sorted(best)
    base = 2 * m
    nA = len(SA)
    Bidx = {L: base + nA + k for k, L in enumerate(sorted(Bset))}
    E = list(edges)
    for t, P in enumerate(SA):
        x = base + t
        for L in point_lines[P]:
            E.append((x, Bidx[L]) if L in Bset else (x, m + L))
    for L, b in Bidx.items():
        for Q in line_points[L]:
            E.append((Q, b))
    n = base + nA + len(Bset)
    return n, E


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(cand):
        nonlocal best, best_n
        if cand is None:
            return
        n, e = cand
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3 and d >= 3:
        q = max(x for x in range(2, d) if lib.is_prime_power(x))
        consider(_arc_graph(q, d))
        consider(_mixed(q, d, deadline, rng))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
