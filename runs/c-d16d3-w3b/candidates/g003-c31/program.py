import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. A set S of points with
# every line holding <= s points of S, and every point on <= s lines indexed by
# S, yields extra A-vertices (one per point of S) and B-vertices (one per line
# of S), each of degree q+1. Diameter stays 3.
# ----------------------------------------------------------------------------

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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Helpers: bipartition, greedy fill, cross-edge saturation.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


def _cross_saturate(n, edges, d, n_new, rng):
    """Add random cross edges (touching a vertex >= n_new) while degree allows; return new edge list."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    col = _bipartition(n, adj)
    have = set()
    for u, v in edges:
        have.add((u, v) if col[u] == 0 else (v, u))
    L = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R
             if (a, b) not in have and (a >= n_new or b >= n_new)]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return out


# ----------------------------------------------------------------------------
# NEW (bold): vertex insertion with simulated-annealing repair.
#
# Rather than building a new algebraic family, grow the best valid graph one
# pair of vertices at a time. Add an A-vertex x and a B-vertex y joined by an
# edge, attach each to opposite-side vertices (freeing a slot where needed),
# then anneal over degree-preserving 2-switches and slot-moves that minimise
# the number of pairs at distance > D. Accept a pair only if the result passes
# lib.is_valid. Every accepted step is an exact valid graph, so the fallback
# always stays valid.
# ----------------------------------------------------------------------------

def _bad_pairs_fast(n, adj, D):
    """Ordered count of vertex pairs at distance > D (bitmask BFS); zero means diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _saturate_sets(n, adj, d, colour, rng):
    """Add cross edges between spare-degree vertices of opposite colour (never hurts distances)."""
    A = [v for v in range(n) if colour[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if colour[v] == 1 and len(adj[v]) < d]
    rng.shuffle(A)
    rng.shuffle(B)
    for a in A:
        if len(adj[a]) >= d:
            continue
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)


def _anneal_sets(n, adj, colour, d, D, rng, deadline, iters):
    """Anneal a bipartite graph (sets) toward diameter <= D. Returns True on success."""
    A = [v for v in range(n) if colour[v] == 0]
    B = [v for v in range(n) if colour[v] == 1]
    if not A or not B:
        return False
    _saturate_sets(n, adj, d, colour, rng)
    cost = _bad_pairs_fast(n, adj, D)
    T = 3.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.2, T * 0.997)
        a = rng.choice(A)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        if rng.random() < 0.5:
            # Degree-preserving 2-switch: (a,b),(a2,b2) -> (a,b2),(a2,b).
            a2 = rng.choice(A)
            if a2 == a or not adj[a2]:
                continue
            b2 = rng.choice(tuple(adj[a2]))
            if b2 == b or b2 in adj[a] or a2 in adj[b]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[a2].discard(b2)
            adj[b2].discard(a2)
            adj[a].add(b2)
            adj[b2].add(a)
            adj[a2].add(b)
            adj[b].add(a2)
            new = _bad_pairs_fast(n, adj, D)
            delta = new - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = new
            else:
                adj[a].discard(b2)
                adj[b2].discard(a)
                adj[a2].discard(b)
                adj[b].discard(a2)
                adj[a].add(b)
                adj[b].add(a)
                adj[a2].add(b2)
                adj[b2].add(a2)
        else:
            # Slot move: re-home edge (a,b) to a spare-degree B-vertex b2.
            b2 = rng.choice(B)
            if b2 == b or b2 in adj[a] or len(adj[b2]) >= d:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[a].add(b2)
            adj[b2].add(a)
            new = _bad_pairs_fast(n, adj, D)
            delta = new - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = new
            else:
                adj[a].discard(b2)
                adj[b2].discard(a)
                adj[a].add(b)
                adj[b].add(a)
    return cost == 0


def _grow_graph(base, d, D, seed, deadline):
    """Repeatedly add a valid (A,B) vertex pair, repaired by annealing. Returns the largest valid graph."""
    n, edges = base
    rng = random.Random(seed * 15485863 + d * 31 + D)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    colour = _bipartition(n, [list(s) for s in adj])
    best = (n, list(edges))
    fails = 0
    while time.monotonic() < deadline and fails < 60:
        tn = n + 2
        x, y = n, n + 1
        tadj = [set(s) for s in adj] + [set(), set()]
        tcol = colour + [0, 1]
        tadj[x].add(y)
        tadj[y].add(x)
        for z, pool_colour in ((x, 1), (y, 0)):
            pool = [v for v in range(n) if colour[v] == pool_colour]
            rng.shuffle(pool)
            k = 0
            for w in pool:
                if k >= d - 1:
                    break
                if len(tadj[w]) >= d:
                    p = rng.choice(tuple(tadj[w]))
                    tadj[w].discard(p)
                    tadj[p].discard(w)
                tadj[w].add(z)
                tadj[z].add(w)
                k += 1
        ok = _anneal_sets(tn, tadj, tcol, d, D, rng, deadline, iters=700)
        if ok:
            e_t = [(u, v) for u in range(tn) for v in tadj[u] if u < v]
            if lib.is_valid(tn, e_t, d, D):
                adj, colour, n = tadj, tcol, tn
                best = (n, e_t)
                fails = 0
                continue
        fails += 1
    return best


# ----------------------------------------------------------------------------
# Baseline pipeline (arc extension + fill + cross-saturation chain).
# ----------------------------------------------------------------------------

def _base_graph(d, D, seed, deadline):
    """Best valid baseline graph found before the deadline (always valid)."""
    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D < 3:
        return fallback
    rng = random.Random(seed * 7919 + d)
    best = fallback
    cands = _arc_extensions(d, deadline, rng)
    cands.sort(key=lambda t: -t[0])
    for n_c, e_c in cands:
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            break
    if best[0] <= 2:
        return best
    n_arc = best[0]
    n_f, e_f = _fill(best[0], best[1], d, D, deadline, random.Random(seed * 104729 + d))
    if n_f > best[0] and lib.is_valid(n_f, e_f, d, D):
        best = (n_f, e_f)
    trial_rng = random.Random(seed * 31337 + d)
    while time.monotonic() < deadline:
        n_b, e_b = best
        e_sat = _cross_saturate(n_b, e_b, d, n_arc, trial_rng)
        if len(e_sat) == len(e_b):
            break
        n_s, e_s = _fill(n_b, e_sat, d, D, deadline, trial_rng)
        if n_s > n_b and lib.is_valid(n_s, e_s, d, D):
            best = (n_s, e_s)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        fallback = (1, [])

    # Stage 1: baseline construction, given roughly the first third of the budget.
    try:
        base = _base_graph(d, D, seed, start + 0.35 * time_limit)
    except Exception:
        base = fallback
    if not lib.is_valid(base[0], base[1], d, D):
        base = fallback

    # Stage 2: grow by annealed vertex-pair insertion until near the deadline.
    try:
        grown = _grow_graph(base, d, D, seed, end)
    except Exception:
        grown = base

    if grown[0] > base[0] and lib.is_valid(grown[0], grown[1], d, D):
        return grown
    return base
