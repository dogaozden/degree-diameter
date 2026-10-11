import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------

def _to_edges(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _k_dd(d):
    """K_{d,d}: diameter 2, a safe fallback for D >= 2."""
    if d < 1:
        return 1, []
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _pg_base(q):
    """Point-line incidence graph of PG(2, q) as adjacency sets.

    Points are 0..m-1, lines are m..2m-1 (line j has vertex m + j, and line j
    uses the same projective vector as point j).
    """
    m2, edges = lib.projective_plane_incidence(q)
    m = m2 // 2
    adj = [set() for _ in range(m2)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return m, adj


def _conic(q, index, F):
    """Conic Y^2 = XZ (plus the nucleus for even q): a 2-arc of size q+1 (q odd) or q+2 (q even)."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _greedy_arc(m, base_adj, s, rng, trials, deadline):
    """Randomized greedy S (point indices) with at most s S-points per line and at most s
    S-lines through any point. Adding P gives A-load on its lines and B-load on the points of line P."""
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
            lines = [L - m for L in base_adj[P]]
            pts = list(base_adj[m + P])
            if all(cl[L] < s for L in lines) and all(cp[Q] < s for Q in pts):
                S.append(P)
                for L in lines:
                    cl[L] += 1
                for Q in pts:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _arc_graph(m, base_adj, S):
    """Old PG incidence plus, per P in S, an A-vertex on the pencil of P and a B-vertex on line P.

    A-vertices are colour 0 (point side), B-vertices colour 1 (line side).
    """
    adj = [set(a) for a in base_adj]
    col = [0] * m + [1] * m
    for P in S:
        x = len(adj)
        adj.append(set(base_adj[P]))
        col.append(0)
        for L in base_adj[P]:
            adj[L].add(x)
    for j in S:
        x = len(adj)
        adj.append(set(base_adj[m + j]))
        col.append(1)
        for Q in base_adj[m + j]:
            adj[Q].add(x)
    return adj, col


# ----------------------------------------------------------------------------
# New helper: generic vertex insertion by exact set cover of 2-balls.
#
# A new vertex x of colour s with neighbour set N (all of colour 1-s, degree < d)
# is at distance <= 3 from every existing vertex iff the union of the 2-balls
# of the vertices in N covers the whole graph. Adding x never lengthens old
# distances, so a valid graph stays valid. Coverage is checked with bitmasks,
# and the greedy cover is retried with random tie-breaking.
# ----------------------------------------------------------------------------

def _ball2(adj):
    """Bitmask of all vertices within distance 2 of each vertex."""
    n = len(adj)
    b1 = [0] * n
    for v in range(n):
        r = 1 << v
        for u in adj[v]:
            r |= 1 << u
        b1[v] = r
    b2 = [0] * n
    for v in range(n):
        r = b1[v]
        for u in adj[v]:
            r |= b1[u]
        b2[v] = r
    return b2


def _cover(adj, col, d, s, b2, rng, tries):
    """Find <= d neighbours of colour 1-s, with spare degree, whose 2-balls cover everything."""
    n = len(adj)
    full = (1 << n) - 1
    cands = [c for c in range(n) if col[c] != s and len(adj[c]) < d]
    if not cands:
        return None
    for _ in range(tries):
        rng.shuffle(cands)
        left = cands[:]
        covered = 0
        chosen = []
        while covered != full and len(chosen) < d and left:
            best_i, best_g = -1, 0
            for i, c in enumerate(left):
                g = (b2[c] & ~covered).bit_count()
                if g > best_g:
                    best_g, best_i = g, i
            if best_i < 0:
                break
            c = left.pop(best_i)
            chosen.append(c)
            covered |= b2[c]
        if covered == full:
            return chosen
    return None


def _grow(adj, col, d, rng, deadline):
    """Repeatedly insert vertices by exact cover until no insertion succeeds or time runs out."""
    while time.monotonic() < deadline:
        b2 = _ball2(adj)
        sides = [0, 1]
        rng.shuffle(sides)
        added = False
        for s in sides:
            ch = _cover(adj, col, d, s, b2, rng, 4)
            if ch is not None:
                x = len(adj)
                adj.append(set(ch))
                col.append(s)
                for c in ch:
                    adj[c].add(x)
                added = True
                break
        if not added:
            break


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    best = _k_dd(d)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D < 3:
        return best

    # Diameter-3 family: PG(2, q) with q + 1 <= d, plus spare-degree arc extensions
    # and generic cover-based growth.
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    qs.sort(reverse=True)
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, base_adj = _pg_base(q)
        options = [[]]
        if s >= 1:
            options.append(_greedy_arc(m, base_adj, s, rng, 30, deadline))
        if s >= 2:
            F = lib.GF(q)
            index = {v: i for i, v in enumerate(lib.projective_points(q))}
            options.append(_conic(q, index, F))

        for S in options:
            if time.monotonic() > deadline:
                break
            adj, col = _arc_graph(m, base_adj, S)
            if max(len(a) for a in adj) > d:
                continue
            _grow(adj, col, d, rng, deadline)
            consider(len(adj), _to_edges(adj))

    if not lib.is_valid(best[0], best[1], d, D):
        best = _k_dd(d)
    return best
