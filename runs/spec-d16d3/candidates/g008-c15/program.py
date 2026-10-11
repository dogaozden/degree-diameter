import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3, bipartite).
# ----------------------------------------------------------------------------

def _pg_graph(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
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
    """Candidate (n, edges) graphs: PG(2,q) plus arc-based extra vertices, one per prime power q."""
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
# Bipartition helper.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


# ----------------------------------------------------------------------------
# Bold branch (D = 3): grow the base by 2 vertices (one per side), then anneal
# edge moves that keep degrees <= d, minimizing the number of pairs violating
# the diameter-3 bipartite condition:
#   same-side pairs need distance <= 2, opposite-side pairs need distance <= 3.
# ----------------------------------------------------------------------------

def _d3_bad(n, adj, colour):
    """Number of unordered vertex pairs violating the bipartite diameter-3 condition."""
    A = 0
    B = 0
    for v in range(n):
        if colour[v]:
            B |= 1 << v
        else:
            A |= 1 << v
    nb = [0] * n
    for v in range(n):
        x = 0
        for w in adj[v]:
            x |= 1 << w
        nb[v] = x
    ball2 = [0] * n  # vertices within distance 2 of u
    for u in range(n):
        x = 1 << u
        for w in adj[u]:
            x |= nb[w] | (1 << w)
        ball2[u] = x
    total = 0
    for v in range(n):
        x = 1 << v  # within distance 3 of v: union of ball2 over neighbours
        for u in adj[v]:
            x |= ball2[u]
        if colour[v] == 0:
            same, opp = A, B
        else:
            same, opp = B, A
        total += (same & ~ball2[v]).bit_count() + (opp & ~x).bit_count()
    return total // 2


def _sa_extend(n0, e0, d, deadline, rng):
    """Add one vertex per side, then anneal edges until no bad pair remains. Returns (n, edges) or None."""
    adjl = [[] for _ in range(n0)]
    for u, v in e0:
        adjl[u].append(v)
        adjl[v].append(u)
    colour = _bipartition(n0, adjl) + [0, 1]
    n = n0 + 2
    adj = [set(a) for a in adjl] + [set(), set()]
    for v in (n0, n0 + 1):
        opp = 1 - colour[v]
        cands = [w for w in range(n0) if colour[w] == opp and len(adj[w]) < d]
        rng.shuffle(cands)
        for w in cands[:min(3, d)]:
            adj[v].add(w)
            adj[w].add(v)
    if d > 0 and len(adj[n0]) < d and len(adj[n0 + 1]) < d:
        adj[n0].add(n0 + 1)
        adj[n0 + 1].add(n0)

    L = [v for v in range(n) if colour[v] == 0]
    R = [v for v in range(n) if colour[v] == 1]
    cur = _d3_bad(n, adj, colour)
    T = 0.5
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        x = rng.randrange(n)
        opp = R if colour[x] == 0 else L
        if len(adj[x]) < d and (not adj[x] or rng.random() < 0.5):
            # Add move.
            zs = [z for z in opp if len(adj[z]) < d and z not in adj[x]]
            if not zs:
                continue
            z = rng.choice(zs)
            adj[x].add(z)
            adj[z].add(x)
            c2 = _d3_bad(n, adj, colour)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                adj[x].discard(z)
                adj[z].discard(x)
        else:
            # Swap move: drop edge x-y, add edge x-z.
            if not adj[x]:
                continue
            y = rng.choice(list(adj[x]))
            zs = [z for z in opp if z != y and len(adj[z]) < d and z not in adj[x]]
            if not zs:
                continue
            z = rng.choice(zs)
            adj[x].discard(y)
            adj[y].discard(x)
            adj[x].add(z)
            adj[z].add(x)
            c2 = _d3_bad(n, adj, colour)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                adj[x].discard(z)
                adj[z].discard(x)
                adj[x].add(y)
                adj[y].add(x)

    edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _pg_graph(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_extensions(d, start + 0.25 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

        # Bold branch: annealed one-vertex-per-side growth for diameter 3.
        if D == 3 and best_n < lib._moore_bound(d, D):
            while time.monotonic() < deadline - 0.5:
                slice_end = min(deadline, time.monotonic() + 6.0)
                res = _sa_extend(best_n, best_e, d, slice_end, rng)
                if res is not None:
                    consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
