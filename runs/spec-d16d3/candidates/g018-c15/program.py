import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base construction (D = 3): arc-extended projective plane incidence graphs.
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. For a point set S with
# every line holding <= s points of S and every point on <= s lines of S, add
# a new A-vertex per P in S (joined to the q+1 lines through P) and a new
# B-vertex per j in S (joined to the q+1 points on line j). Diameter stays 3.
#
# New bold step: AUGMENTATION. Adding a vertex never increases distances between
# old vertices, so a new vertex v is safe iff it reaches every old vertex within
# distance 3. Choose v's neighbours N (all on one side, all with spare degree) so
# that the radius-2 balls of N cover all old vertices. This is a randomized greedy
# set cover over bitmasks, and it repeats while time remains.
# ----------------------------------------------------------------------------

def _pg(q):
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
    """True if every line holds <= s points of S and every point lies on <= s lines of S."""
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
    for t, j in enumerate(S):  # S is also a set of line indices
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, rng, deadline):
    """Return a list of (n, edges) base graphs for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, pl, lp, index, _pts = _pg(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            cands.append(cs)
        for S in cands:
            if _loads_ok(S, s, m, pl, lp):
                out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Augmentation: add vertices whose radius-2 balls cover everything.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
    """Return a 2-colouring of a bipartite graph given as adjacency sets."""
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


def _cover(cand, R2, target, d, rng):
    """Randomized greedy: pick <= d candidates whose radius-2 balls cover target. Return chosen or None."""
    covered = 0
    chosen = []
    avail = set(cand)
    for _ in range(d):
        if covered == target:
            break
        scored = []
        for y in avail:
            g = (R2[y] & ~covered).bit_count()
            if g > 0:
                scored.append((g, rng.random(), y))
        if not scored:
            break
        scored.sort(reverse=True)
        if rng.random() < 0.7:
            y = scored[0][2]
        else:
            y = rng.choice(scored[:5])[2]
        chosen.append(y)
        covered |= R2[y]
        avail.discard(y)
    if covered == target and chosen:
        return chosen
    return None


def _augment(n, edges, d, deadline, rng):
    """Greedily add new vertices while the set-cover test succeeds. Returns (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n, adj)
    fails = 0
    while fails < 30 and time.monotonic() < deadline:
        target = (1 << n) - 1
        M1 = []
        for u in range(n):
            mk = 1 << u
            for w in adj[u]:
                mk |= 1 << w
            M1.append(mk)
        R2 = []
        for u in range(n):
            mk = M1[u]
            for w in adj[u]:
                mk |= M1[w]
            R2.append(mk)

        sides = [0, 1]
        rng.shuffle(sides)
        success = False
        for side in sides:
            cand = [y for y in range(n) if color[y] != side and len(adj[y]) < d]
            if not cand:
                continue
            chosen = _cover(cand, R2, target, d, rng)
            if chosen:
                v = n
                color.append(side)
                adj.append(set())
                for y in chosen:
                    adj[v].add(y)
                    adj[y].add(v)
                n += 1
                success = True
                break
        if success:
            fails = 0
        else:
            fails += 1

    out = []
    for u in range(n):
        for w in adj[u]:
            if u < w:
                out.append((u, w))
    return n, out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) for D = 4 (kept from parent, small q only).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed * 7919 + d * 31 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback[0], fallback[1]

    if D == 3:
        # Base constructions, largest first.
        base_deadline = start + 0.15 * time_limit
        bases = _arc_candidates(d, rng, base_deadline)
        bases.sort(key=lambda t: -t[0])
        valid_bases = []
        for n_c, e_c in bases:
            if lib.is_valid(n_c, e_c, d, D):
                valid_bases.append((n_c, e_c))
                if n_c > best_n:
                    best_n, best_e = n_c, e_c
        # Augment the strongest few bases, sharing the remaining budget.
        work = valid_bases[:3]
        final_deadline = start + 0.6 * time_limit
        for idx, (n_c, e_c) in enumerate(work):
            now = time.monotonic()
            remaining = final_deadline - now
            if remaining <= 0:
                break
            budget = remaining / (len(work) - idx)
            n2, e2 = _augment(n_c, e_c, d, now + budget, rng)
            if n2 > best_n and lib.is_valid(n2, e2, d, D):
                best_n, best_e = n2, e2

    elif D >= 4:
        if D == 4 and d >= 3:
            gq = _best_gq(d)
            if gq is not None and gq[0] > best_n and lib.is_valid(gq[0], gq[1], d, D):
                best_n, best_e = gq[0], gq[1]

    result = (best_n, best_e)
    if not lib.is_valid(result[0], result[1], d, D):
        result = fallback
    return result
