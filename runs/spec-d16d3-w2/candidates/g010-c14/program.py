"""Arc-extended projective-plane graphs with a greedy cover-augmentation search.

Diameter-3 construction (order 2(q^2+q+1) + 2|S|):
  Start from the PG(2, q) point-line incidence graph. Each old vertex has degree q+1,
  so with d >= q+1 there is spare capacity s = d-q-1. Choose an arc S with every line
  holding <= s points of S and every point on <= s lines indexed by S. Add an A-vertex
  per P in S (joined to the q+1 lines through P) and a B-vertex per j in S (joined to
  the q+1 points on line j).

New in this version: a generic cover-augmentation search (_augment).
  A new vertex on side s must be at distance 2 from every other side-s vertex, so its
  neighbourhood must cover them through their neighbours. _cover_neighbors finds such
  a neighbourhood by greedy set cover over opposite-side vertices with spare degree.
  Candidates are kept only if lib.is_valid still passes. Random removals and restarts
  from the best snapshot give an iterated search.

Analysis: with d = 16, q = 13, any side-1 vertex whose neighbourhood covers all points
using at most 16 lines must contain a full star (a blocking set of size <= 16 in PG(2,13)
contains a line). A star at P is available only when every line through P has spare
capacity, so the new vertices are capped by the arc bound 14 per side. Beating 394 would
need edge deletions or a different base, which the augmentation can reach only indirectly.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane data and arc extensions (diameter 3).
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


def _arc_graph(m, edges, S, point_lines, line_points):
    """Extended graph with sides. Points and A-vertices are side 0; lines and B-vertices are side 1."""
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
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_extensions(d, deadline, rng):
    """Return candidates (n, edges, side) for each prime power q with q + 1 <= d."""
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
        n_c, e_c, side_c = _arc_graph(m, edges, S, point_lines, line_points)
        out.append((n_c, e_c, side_c))
    return out


# ----------------------------------------------------------------------------
# Cover augmentation (new): greedy distance-2 cover for new vertices.
# ----------------------------------------------------------------------------

def _valid_adj(adj, d, D):
    """Return (n, edges) relabelled if the graph in adjacency-set form is valid, else None."""
    edges = [(u, v) for u in adj for v in adj[u] if u < v]
    if not edges:
        return None
    n, E = lib.relabel(edges)
    return (n, E) if lib.is_valid(n, E, d, D) else None


def _attach(adj, x, nbrs):
    """Insert vertex x adjacent to nbrs."""
    adj[x] = set(nbrs)
    for u in nbrs:
        adj.setdefault(u, set()).add(x)


def _detach(adj, x):
    """Remove vertex x and its incident edges; drop neighbours that become isolated."""
    nbrs = adj.pop(x)
    for u in nbrs:
        s = adj[u]
        s.discard(x)
        if not s:
            del adj[u]
    return nbrs


def _cover_neighbors(adj, side, s, d, rng):
    """Pick <= d opposite-side vertices with spare degree whose neighbourhoods cover all side-s vertices.

    A new vertex on side s must be at distance exactly 2 from every other side-s vertex,
    so its neighbourhood has to reach all of them through neighbours. Greedy set cover.
    """
    uncovered = {v for v in adj if side[v] == s}
    if not uncovered:
        return None
    cands = [c for c in adj if side[c] != s and len(adj[c]) < d]
    rng.shuffle(cands)
    chosen = []
    remaining = uncovered
    while remaining:
        if len(chosen) >= d:
            return None
        best_c, best_g = None, 0
        for c in cands:
            g = len(adj[c] & remaining)
            if g > best_g:
                best_c, best_g = c, g
        if best_c is None:
            return None
        chosen.append(best_c)
        remaining = remaining - adj[best_c]
        cands.remove(best_c)
    return chosen


def _augment(n0, E0, side0, d, D, deadline, rng):
    """Greedy cover augmentation with validity-checked acceptance and iterated restarts."""
    adj = {}
    side = {}
    for v in range(n0):
        side[v] = side0[v]
    for u, v in E0:
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)
    if _valid_adj(adj, d, D) is None:
        return None

    def snapshot():
        return (len(adj),
                [(u, v) for u in adj for v in adj[u] if u < v],
                {v: side[v] for v in adj})

    best = snapshot()
    nxt = n0
    added = []
    fails = 0
    while time.monotonic() < deadline:
        # Occasional random removal of an added vertex, kept only if the graph stays valid.
        if added and rng.random() < 0.03:
            x = added[rng.randrange(len(added))]
            if x in adj:
                nbr = _detach(adj, x)
                if _valid_adj(adj, d, D) is None:
                    _attach(adj, x, nbr)
                else:
                    added.remove(x)
            continue

        s = rng.randrange(2)
        nb = _cover_neighbors(adj, side, s, d, rng)
        if nb is not None:
            x = nxt
            nxt += 1
            side[x] = s
            _attach(adj, x, nb)
            if _valid_adj(adj, d, D) is not None:
                added.append(x)
                fails = 0
                if len(adj) > best[0]:
                    best = snapshot()
                continue
            _detach(adj, x)
            del side[x]
        fails += 1
        if fails > 200:
            # Restart from the best valid graph found so far.
            _, bestE, bestside = best
            adj.clear()
            for u, v in bestE:
                adj.setdefault(u, set()).add(v)
                adj.setdefault(v, set()).add(u)
            side.clear()
            side.update(bestside)
            nxt = max(side) + 1 if side else n0
            added = [v for v in side if v >= n0]
            fails = 0

    _, bestE, _ = best
    n, E = lib.relabel(bestE)
    return (n, E) if lib.is_valid(n, E, d, D) else None


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    have_arc = False
    if D >= 3:
        cands = _arc_extensions(d, start + 0.25 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c, _side in cands:
            consider(n_c, e_c)
        if cands:
            have_arc = True
            n_c, e_c, side_c = cands[0]
            # For D = 3 the augmentation gets the whole budget; otherwise it gets 60%.
            aug_end = deadline if D == 3 else start + 0.6 * time_limit
            res = _augment(n_c, e_c, side_c, d, D, aug_end,
                           random.Random(seed * 31 + 7))
            if res is not None:
                consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for the remaining cases.
    if not (D == 3 and have_arc):
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
