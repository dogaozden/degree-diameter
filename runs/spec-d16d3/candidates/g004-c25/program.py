import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane bases and the conic arc extension (diameter 3).
#
# PG(2, q) incidence has degree q+1. With spare degree s = d - q - 1, pick an
# arc S (every line holds <= s points of S) and add one point-side vertex A_P
# per P in S (joined to the lines through P) and one line-side vertex B_L per
# L in S (joined to the points on L). Diameter stays 3.
# ----------------------------------------------------------------------------

def _largest_prime_power_below(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _conic_points(q, index):
    """Conic (plus nucleus for even q): an arc with at most 2 points on every line."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(q, S):
    """Incidence graph of PG(2, q) plus A/B vertices for the point set S. Returns (n, edges, side)."""
    n0, base = lib.projective_plane_incidence(q)
    m = n0 // 2
    nbr_line = [[] for _ in range(m)]   # point i -> line vertices m + j
    nbr_pt = [[] for _ in range(m)]     # line j -> point vertices
    for u, v in base:
        nbr_line[u].append(v)
        nbr_pt[v - m].append(u)
    k = len(S)
    E = list(base)
    for t, P in enumerate(S):
        a = n0 + t
        for v in nbr_line[P]:
            E.append((a, v))
    for t, j in enumerate(S):
        b = n0 + k + t
        for u in nbr_pt[j]:
            E.append((u, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n0 + 2 * k, E, side


# ----------------------------------------------------------------------------
# Bold step (D = 3): add one point-side and one line-side vertex to a valid
# graph, then anneal the edges with degree-preserving double-edge swaps,
# minimising the number of pairs at distance > 3.
# ----------------------------------------------------------------------------

def _add_pair(n, edges, side):
    """Append a point-side vertex n and a line-side vertex n+1 with no edges yet."""
    return n + 2, list(edges), list(side) + [0, 1]


def _anneal(n, edges, side, d, D, deadline, rng):
    """Try to reach zero bad pairs by degree-preserving swaps; return (n, edges) or None."""
    eset = set()
    elist = []
    deg = [0] * n
    for u, v in edges:
        p, l = (u, v) if side[u] == 0 else (v, u)
        if (p, l) in eset:
            continue
        eset.add((p, l))
        elist.append((p, l))
        deg[p] += 1
        deg[l] += 1

    # Saturate spare degree with new edges (adding edges never hurts diameter).
    pts = [v for v in range(n) if side[v] == 0 and deg[v] < d]
    lns = [v for v in range(n) if side[v] == 1 and deg[v] < d]
    rng.shuffle(lns)
    for p in pts:
        for l in lns:
            if deg[p] >= d:
                break
            if deg[l] < d and (p, l) not in eset:
                eset.add((p, l))
                elist.append((p, l))
                deg[p] += 1
                deg[l] += 1

    cur = lib.bad_pairs(n, elist, D)
    T = 0.7
    while cur > 0 and time.monotonic() < deadline and len(elist) >= 2:
        i = rng.randrange(len(elist))
        j = rng.randrange(len(elist))
        if i == j:
            continue
        p1, l1 = elist[i]
        p2, l2 = elist[j]
        if p1 == p2 or l1 == l2:
            continue
        if (p1, l2) in eset or (p2, l1) in eset:
            continue
        # Apply swap: (p1,l1),(p2,l2) -> (p1,l2),(p2,l1). Degrees unchanged.
        elist[i] = (p1, l2)
        elist[j] = (p2, l1)
        eset.discard((p1, l1))
        eset.discard((p2, l2))
        eset.add((p1, l2))
        eset.add((p2, l1))
        c2 = lib.bad_pairs(n, elist, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            elist[i] = (p1, l1)
            elist[j] = (p2, l2)
            eset.discard((p1, l2))
            eset.discard((p2, l1))
            eset.add((p1, l1))
            eset.add((p2, l2))

    if cur == 0:
        return n, list(elist)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 5.0)
    deadline = start + max(0.5, budget)
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D < 2:
        return (2, [(0, 1)]) if D == 1 else (1, [])

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, e0, [0] * d + [1] * d)

    def consider(n, e, side):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e, side)

    if D == 2:
        return best[0], best[1]

    # D >= 3: projective plane base, then the conic arc extension if spare degree allows.
    q = _largest_prime_power_below(d)
    if q is not None and q <= 31:
        m = (lib.projective_plane_incidence(q)[0]) // 2
        n_pg, e_pg = lib.projective_plane_incidence(q)
        consider(n_pg, e_pg, [0] * m + [1] * m)

        s = d - q - 1
        if s >= 2:
            pts = lib.projective_points(q)
            index = {p: i for i, p in enumerate(pts)}
            S = _conic_points(q, index)
            n_a, e_a, side_a = _arc_graph(q, S)
            consider(n_a, e_a, side_a)

    # Bold step for D = 3: try to exceed the current best by annealing a grown graph.
    moore = 2 * sum((d - 1) ** i for i in range(D)) if d >= 2 else 2
    if D == 3 and best[0] < moore and time.monotonic() < deadline:
        cur_n, cur_e, cur_side = best
        while time.monotonic() < deadline:
            n2, e2, side2 = _add_pair(cur_n, cur_e, cur_side)
            if n2 > moore:
                break
            res = _anneal(n2, e2, side2, d, D, deadline, rng)
            if res is None:
                break
            n_new, e_new = res
            if not lib.is_valid(n_new, e_new, d, D):
                break
            best = (n_new, e_new, side2)
            cur_n, cur_e, cur_side = best

    n, e, _ = best
    if lib.is_valid(n, e, d, D):
        return n, e
    return lib.haar_graph(d, range(d))
