"""Arc-extended PG(2,q) construction with a new monotone growth step.

New helper, _grow: adding a vertex never increases any distance between existing
vertices, so a new vertex is safe to add whenever its neighbours (on the opposite
side, with spare degree) reach every existing vertex within D steps. _grow picks
such neighbours greedily by set cover over the (D-1)-balls of the candidates. It
can use spare capacity on both sides, including vertices added earlier, so new
vertices may attach to earlier extra vertices as well as to base vertices.

Calibration: d=3, D=3 gives PG(2,2), order 14. For d=16, D=3 the arc-extended
base reaches 394 and the growth step is tried on top of it. Every returned
graph is checked with lib.is_valid, with a K_{d,d} fallback.
"""
import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc construction (D = 3), as in the parent.
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
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex (on lines through it)
    and a B-vertex (joined to points of the line). Returns (n, edges, side)."""
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
# New helper: monotone growth by set cover.
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _balls(n, adj, r):
    """reach[v] = bitmask of vertices within distance r of v."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        nxt = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            nxt.append(x)
        reach = nxt
    return reach


def _grow(n, adj, side, d, D, rng, deadline, max_fail=40):
    """Monotone growth. A new vertex v on side s is joined to a set of opposite-side
    vertices u with spare degree, chosen greedily so that every existing vertex lies
    within D-1 of some chosen u (hence within D of v). Adding v never lengthens an
    existing shortest path, so the diameter bound is kept. Modifies adj in place.
    Returns (n, adj, side)."""
    side = list(side)
    fails = 0
    while fails < max_fail and time.monotonic() < deadline:
        R = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        s = rng.randint(0, 1)
        cands = [u for u in range(n) if side[u] != s and len(adj[u]) < d]
        covered = 0
        chosen = []
        while covered != full and cands and len(chosen) < d:
            best_g, pick = 0, []
            for u in cands:
                g = (R[u] & ~covered).bit_count()
                if g > best_g:
                    best_g, pick = g, [u]
                elif g == best_g and g > 0:
                    pick.append(u)
            if best_g == 0:
                break
            u = rng.choice(pick)
            chosen.append(u)
            cands.remove(u)
            covered |= R[u]
        if covered == full and chosen:
            v = n
            n += 1
            adj.append(set())
            side.append(s)
            for u in chosen:
                adj[u].add(v)
                adj[v].add(u)
            fails = 0
        else:
            fails += 1
    return n, adj, side


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

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

    arc_base = None
    if D >= 3:
        cands = _arc_candidates(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands:
            consider(n_c, E_c)
        if cands and lib.is_valid(cands[0][0], cands[0][1], d, D):
            arc_base = cands[0]

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Growth on top of the arc base: repeated randomized set-cover attempts.
    if D == 3 and arc_base is not None:
        base_n, base_E, base_side = arc_base
        attempts = 0
        while time.monotonic() < deadline and attempts < 200:
            attempts += 1
            adj = _to_adj(base_n, base_E)
            n2, adj2, _ = _grow(base_n, adj, base_side, d, D, rng, deadline)
            if n2 > best_n:
                E2 = [(x, y) for x in range(n2) for y in adj2[x] if x < y]
                consider(n2, E2)

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
