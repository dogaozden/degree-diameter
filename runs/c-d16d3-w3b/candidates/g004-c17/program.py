import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. For a point set S with
# every line holding <= s points of S and every point on <= s lines indexed by
# S, add an A-vertex per P in S (joined to the q+1 lines through P) and a
# B-vertex per j in S (joined to the q+1 points on line j). Diameter stays 3.
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
# NEW construction: Haar-type bi-Cayley graphs from difference covers.
#
# Let G be a group of order m and S a d-subset of G. Join a_g to b_{g s} for
# s in S. Then:
#   * a_g, a_h are at distance 2 iff h is in S S^{-1} (times g),
#   * b_g, b_h are at distance 2 iff g^{-1} h is in S^{-1} S,
#   * a_g, b_h are at distance <= 3 as soon as S S^{-1} = G.
# So if both S S^{-1} = G and S^{-1} S = G, the graph is d-regular, bipartite,
# has 2m vertices and diameter 3. Since |S S^{-1}| <= d(d-1)+1, we have
# m <= d(d-1)+1, i.e. order <= the Moore bound. We search for such S by
# simulated annealing, for increasing m, starting just above the arc graph.
# Groups are semidirect products Z_a x| Z_k (lib.semidirect_group), which
# include all cyclic and all abelian groups of the form Z_a x Z_k (r = 1).
# ----------------------------------------------------------------------------

def _group_options(m):
    """All (a, k, r) with a * k = m that lib.semidirect_group accepts."""
    opts = []
    for k in range(1, m + 1):
        if m % k:
            continue
        a = m // k
        if a == 1:
            opts.append((1, k, 0))
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                opts.append((a, k, r))
    return opts


def _tables(a, k, r):
    """Multiplication and inverse tables of Z_a x|_r Z_k; identity is element 0."""
    order, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return order, M, I


def _bump(arr, g, delta):
    """Change arr[g] by delta; return the change in the number of uncovered entries."""
    old = arr[g]
    new = old + delta
    arr[g] = new
    if old == 0 and new > 0:
        return -1
    if old > 0 and new == 0:
        return 1
    return 0


def _cover_sa(m, k, M, I, rng, deadline, iters):
    """Find S, |S| = k, in a group of order m with S S^{-1} = G and S^{-1} S = G; None on failure."""
    S = rng.sample(range(m), k)
    inS = [False] * m
    for s in S:
        inS[s] = True
    c1 = [0] * m  # counts of a b^{-1} over ordered pairs a != b in S
    c2 = [0] * m  # counts of a^{-1} b over ordered pairs a != b in S
    for i in range(k):
        for j in range(k):
            if i != j:
                a, b = S[i], S[j]
                c1[M[a][I[b]]] += 1
                c2[M[I[a]][b]] += 1
    cost = sum(1 for g in range(1, m) if c1[g] == 0) + sum(1 for g in range(1, m) if c2[g] == 0)

    def touch(x, others, delta):
        """Add (delta = +1) or remove (delta = -1) the pair contributions of x against others."""
        dc = 0
        ix = I[x]
        for s in others:
            is_ = I[s]
            dc += _bump(c1, M[x][is_], delta)
            dc += _bump(c1, M[s][ix], delta)
            dc += _bump(c2, M[ix][s], delta)
            dc += _bump(c2, M[is_][x], delta)
        return dc

    T0, T1 = 1.5, 0.05
    for it in range(iters):
        if cost == 0:
            break
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        while inS[y]:
            y = rng.randrange(m)
        others = S[:i] + S[i + 1:]
        delta = touch(x, others, -1) + touch(y, others, +1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS[x] = False
            inS[y] = True
            cost += delta
        else:
            touch(y, others, -1)
            touch(x, others, +1)
    if cost == 0:
        return S
    return None


def _haar_edges(m, M, S):
    """Bi-Cayley graph: a_g (vertex g) joined to b_{g s} (vertex m + g s) for s in S."""
    edges = []
    for g in range(m):
        for s in S:
            edges.append((g, m + M[g][s]))
    return 2 * m, edges


def _diff_cover_search(d, m_lo, deadline, rng):
    """For m = m_lo, m_lo+1, ... find a group of order m with a d-set of full covering; return (n, edges)."""
    best = None
    bound = d * (d - 1) + 1
    m = max(m_lo, d + 1)
    while m <= bound and time.monotonic() < deadline:
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, (deadline - now) / 2))
        opts = _group_options(m)
        found = None
        while found is None and opts and time.monotonic() < slice_end:
            a, k, r = rng.choice(opts)
            order, M, I = _tables(a, k, r)
            S = _cover_sa(order, d, M, I, rng, slice_end, iters=20000)
            if S is not None:
                found = _haar_edges(order, M, S)
        if found is None:
            break
        best = found
        m += 1
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    if D >= 3:
        # Arc-extended projective plane graphs (order 394 for d = 16).
        for n_c, e_c in _arc_extensions(d, start + 0.2 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

        # New construction: Haar-type bi-Cayley graph from a difference cover.
        # Start just above the current best order so that every success is an improvement.
        res = _diff_cover_search(d, best_n // 2 + 1, deadline,
                                 random.Random(seed * 104729 + d))
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
