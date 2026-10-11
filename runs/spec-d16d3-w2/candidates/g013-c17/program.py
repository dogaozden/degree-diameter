import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bounds and projective-plane arc construction (inherited from parent)
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


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
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex and a B-vertex.
    Returns (n, edges, side) with side 0 = A-type, side 1 = B-type."""
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
# NEW helper: diameter-3 vertex-pair augmentation by set cover.
#
# In a bipartite graph of diameter 3, adding a new vertex x on side 0 whose
# neighbourhood N lies on side 1 keeps the diameter at most 3 for all pairs
# involving x if and only if N "covers" side 0: every old side-0 vertex shares
# a neighbour with x (old same-side distances are at most 2, so this is the
# only requirement for same-side pairs; cross-side pairs are then at most 3).
# Symmetrically, a new side-1 vertex y with neighbourhood M must cover side 1.
# A final edge check between N and M gives dist(x, y) <= 3.
#
# Adding vertices never lengthens old distances, so each accepted pair keeps
# the diameter bound. The covers are found by randomized greedy with
# bitmask gains and random tie-breaking; restarts are cheap.
#
# Projective-plane pencils (lines through a point, points on a line) are
# exact covers of this type, so the search can in principle reach them.
# If no cover is found, the base graph is returned unchanged.
# ----------------------------------------------------------------------------

def _try_cover(targets, cands, nbrs, d, rng):
    """Pick at most d candidates whose neighbourhoods (in `nbrs`) cover all `targets`.
    Returns the chosen candidate list, or None."""
    pos = {t: i for i, t in enumerate(targets)}
    full = (1 << len(targets)) - 1
    avail = {}
    for c in cands:
        mask = 0
        for u in nbrs[c]:
            i = pos.get(u)
            if i is not None:
                mask |= 1 << i
        if mask:
            avail[c] = mask
    covered = 0
    chosen = []
    noise = 2.0 * rng.random()
    while covered != full:
        if len(chosen) >= d:
            return None
        best = None
        best_score = -1.0
        for c, mask in avail.items():
            gain = (mask & ~covered).bit_count()
            if gain == 0:
                continue
            score = gain + noise * rng.random()
            if score > best_score:
                best_score = score
                best = c
        if best is None:
            return None
        chosen.append(best)
        covered |= avail.pop(best)
    return chosen


def _add_pair(n, adj, side, d, rng):
    """Try to add one side-0 vertex x and one side-1 vertex y. Returns new adjacency or None."""
    side0 = [v for v in range(n) if side[v] == 0]
    side1 = [v for v in range(n) if side[v] == 1]
    cand = [c for c in side1 if len(adj[c]) < d]
    N = _try_cover(side0, cand, adj, d, rng)
    if N is None:
        return None
    x, y = n, n + 1
    adj2 = [set(s) for s in adj]
    adj2.append(set())
    adj2.append(set())
    for c in N:
        adj2[c].add(x)
        adj2[x].add(c)
    cand2 = [c for c in side0 + [x] if len(adj2[c]) < d]
    M = _try_cover(side1, cand2, adj2, d, rng)
    if M is None:
        return None
    # dist(x, y) <= 3 requires an edge between N and M (or x in M).
    if not any(b in adj2[a] for a in N for b in M):
        return None
    for c in M:
        adj2[c].add(y)
        adj2[y].add(c)
    return adj2


def _augment(n, adj, side, d, moore_bound, rng, deadline, max_tries=3000):
    """Repeatedly add valid vertex pairs while time and the Moore bound allow.
    Returns (n, adj, side) of the final graph."""
    side = list(side)
    while n + 2 <= moore_bound and time.monotonic() < deadline:
        new_adj = None
        tries = 0
        while new_adj is None and tries < max_tries and time.monotonic() < deadline:
            new_adj = _add_pair(n, adj, side, d, rng)
            tries += 1
        if new_adj is None:
            break
        adj = new_adj
        n += 2
        side += [0, 1]
    return n, adj, side


def _edges_of(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    if D < 3:
        return best_n, list(best_E)

    # Arc-extended projective-plane bases (diameter 3, valid for any D >= 3).
    cands = _arc_candidates(d, start + 0.1 * time_limit, random.Random(seed * 7919 + d))
    cands.sort(key=lambda t: -t[0])
    base = None
    for n_c, E_c, side_c in cands:
        if n_c > best_n and lib.is_valid(n_c, E_c, d, D):
            best_n, best_E = n_c, E_c
            if base is None:
                base = (n_c, E_c, side_c)

    if base is not None:
        n0, E0, side0 = base
        adj = [set() for _ in range(n0)]
        for u, v in E0:
            adj[u].add(v)
            adj[v].add(u)
        mb = _moore(d, D)
        # Augment in stages so each accepted state is checked independently.
        n, cur_adj, cur_side = n0, adj, list(side0)
        while n + 2 <= mb and time.monotonic() < deadline:
            n_new, adj_new, side_new = _augment(n, cur_adj, cur_side, d, mb, rng,
                                                deadline, max_tries=400)
            if n_new == n:
                break
            E_new = _edges_of(n_new, adj_new)
            if not lib.is_valid(n_new, E_new, d, D):
                break
            if n_new > best_n:
                best_n, best_E = n_new, E_new
            n, cur_adj, cur_side = n_new, adj_new, side_new

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
