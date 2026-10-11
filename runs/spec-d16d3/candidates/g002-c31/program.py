"""Bold variant for d=16, D=3: a deletion-based annealing search inside PG(2,16),
seeded by the arc-extended PG(2,q) family.

Families used (all verified with lib.is_valid before being kept):
  1. K_{d,d} (diameter 2) as a safe fallback.
  2. PG(2, d-1) incidence when d-1 is a prime power (degree exactly d).
  3. Conic arc extensions of PG(2, q) with spare degree s = d-q-1 >= 2:
     new A-vertices for conic points (joined to their lines) and new B-vertices
     for dual-conic lines (joined to their points). Diameter stays 3.
  4. Deletion annealing: start from PG(2, d) (degree d+1), keep random subsets of
     points and lines, and minimise bad_pairs + degree excess - size. Any state
     with zero bad pairs and zero excess is a valid bipartite graph.
"""
import math
import random
import time

import lib


def _take(best, cand, d, D):
    """Return cand if it is a valid graph larger than best, otherwise best."""
    if cand is None:
        return best
    n, e = cand
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


def _pg_lists(q):
    """Incidence edges plus point->lines and line->points lists for PG(2, q).

    Points are 0..m-1 and lines are m..2m-1 in the returned edges.
    """
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pt_lines = [[] for _ in range(m)]
    line_pts = [[] for _ in range(m)]
    for u, v in edges:
        pt_lines[u].append(v - m)
        line_pts[v - m].append(u)
    return m, edges, pt_lines, line_pts


def _conic_extension(q, d):
    """Arc-extended PG(2, q) graph with spare degree s = d - q - 1 >= 2, or None."""
    s = d - q - 1
    if s < 2 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    m, edges, pt_lines, line_pts = _pg_lists(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pt_lines[P]:
            cl[L] += 1
        for Q in line_pts[P]:
            cp[Q] += 1
    if max(cl) > s or max(cp) > s:
        return None
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pt_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_pts[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def _evaluate(m, pt_lines, inA, inB, d, D):
    """Build the induced subgraph on kept points/lines and return (n, edges, bad, excess)."""
    pidx = [-1] * m
    lidx = [-1] * m
    n = 0
    for p in range(m):
        if inA[p]:
            pidx[p] = n
            n += 1
    for l in range(m):
        if inB[l]:
            lidx[l] = n
            n += 1
    edges = []
    for p in range(m):
        if inA[p]:
            for l in pt_lines[p]:
                if inB[l]:
                    edges.append((pidx[p], lidx[l]))
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    excess = sum(x - d for x in deg if x > d)
    bad = lib.bad_pairs(n, edges, D) if n > 1 else 0
    return n, edges, bad, excess


def _deletion_search(q, d, D, rng, deadline):
    """Simulated annealing over subsets of PG(2, q) points and lines.

    Score (minimised): 4*bad + 30*excess - size. Returns the largest state found
    with bad == 0 and excess == 0, as (n, edges), or None.
    """
    m, _, pt_lines, _ = _pg_lists(q)
    inA = [rng.random() < 0.8 for _ in range(m)]
    inB = [rng.random() < 0.8 for _ in range(m)]

    def score(r):
        return 4 * r[2] + 30 * r[3] - r[0]

    fc = score(_evaluate(m, pt_lines, inA, inB, d, D))
    best = None
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 3.0, 0.1
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        side = inA if rng.random() < 0.5 else inB
        i = rng.randrange(m)
        side[i] = not side[i]
        res = _evaluate(m, pt_lines, inA, inB, d, D)
        fn = score(res)
        if fn <= fc or rng.random() < math.exp(-(fn - fc) / T):
            fc = fn
            if res[2] == 0 and res[3] == 0 and (best is None or res[0] > best[0]):
                best = (res[0], res[1])
        else:
            side[i] = not side[i]
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        # Plain projective plane of order d-1 (degree exactly d).
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            best = _take(best, lib.projective_plane_incidence(q), d, D)
        # Conic arc extensions for every smaller prime power.
        for q in range(2, d - 1):
            best = _take(best, _conic_extension(q, d), d, D)

    # Bold family: deletion annealing inside PG(2, d) when d is a prime power.
    if D == 3 and d >= 8 and lib.is_prime_power(d):
        cand = _deletion_search(d, d, D, rng, start + 0.8 * time_limit)
        best = _take(best, cand, d, D)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
