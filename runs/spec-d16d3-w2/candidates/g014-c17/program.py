"""Pencil-arc augmentation of PG(2, q) for diameter-3 bipartite graphs.

Construction (D >= 3, q = largest prime power with q + 1 <= d, s = d - q - 1):
  * Base: incidence graph of PG(2, q), points 0..m-1, lines m..2m-1.
  * X-pencils: for each point P in a set Pi, add a vertex joined to all q+1 lines
    through P. Each line may carry at most s such pencils, so Pi is an s-fold arc.
  * Y-pencils: for each line j in a set Lam, add a vertex joined to all q+1 points
    on j. Each point may lie on at most s lines of Lam.
  * Points and X-pencils form one colour class; lines and Y-pencils form the other.
  * Diameter stays 3: X-pencils are pairwise at distance 2 via the line PP', Y-pencils
    likewise via the common point, and each cross pair is at distance 3 via PQ.

Analysis: any new X-type vertex must reach all points within distance 2, which forces
its neighbourhood to contain a full pencil of lines. The pencil family therefore caps at
2m + 2*(max s-fold arc). For q = 13, s = 2 the arc is a conic of size 14 (Segre), giving
2*183 + 28 = 394. This matches the record and does not beat it. Beating 394 needs a
different base or freed PG edges, which this program does not attempt. The program
always verifies with lib.is_valid and falls back to K_{d,d} or plain PG(2,q).
"""
import random
import time

import lib


def _best_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _incidence_lists(q):
    """Return (m, pl, lp, edges): pl[P] = lines through P, lp[j] = points on line j, both in 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        j = v - m
        pl[u].append(j)
        lp[j].append(u)
    return m, pl, lp, edges


def _conic_seed(q):
    """Conic (plus nucleus for even q) as a point-index set. Valid as an arc and as a dual arc."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _max_set(m, s, item_groups, group_items, init, target, rng, deadline):
    """Large set S of items such that every group contains at most s members of S.

    item_groups[x] lists the groups containing item x. group_items[g] lists the items in group g.
    Local search with plateau moves: a candidate is inserted by removing its blockers
    (one blocker always, two occasionally). Stops at `target` or the deadline.
    """
    load = [0] * m
    inS = [False] * m
    S = []

    def add(x):
        inS[x] = True
        S.append(x)
        for g in item_groups[x]:
            load[g] += 1

    def remove(x):
        inS[x] = False
        S.remove(x)
        for g in item_groups[x]:
            load[g] -= 1

    for x in init:
        if not inS[x] and all(load[g] < s for g in item_groups[x]):
            add(x)
    best = list(S)
    if len(best) >= target:
        return best

    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        sat = [g for g in item_groups[x] if load[g] >= s]
        if not sat:
            add(x)
        else:
            R = []
            for g in sat:
                drop = load[g] - s + 1 - sum(1 for r in R if g in item_groups[r])
                if drop > 0:
                    cand = [r for r in group_items[g] if inS[r] and r not in R]
                    rng.shuffle(cand)
                    R.extend(cand[:drop])
                    if len(R) > 2:
                        break
            if not (1 <= len(R) <= 2):
                continue
            if len(R) == 2 and rng.random() > 0.05:
                continue
            for r in R:
                remove(r)
            add(x)
        if len(S) > len(best):
            best = list(S)
            if len(best) >= target:
                break
    return best


def _pencil_graph(m, pl, lp, base_edges, Pi, Lam):
    """Base PG(2,q) plus X-pencils at Pi and Y-pencils at Lam; returns (n, edges)."""
    edges = list(base_edges)
    k1 = 2 * m
    for t, P in enumerate(Pi):
        v = k1 + t
        for j in pl[P]:
            edges.append((v, m + j))
    k2 = k1 + len(Pi)
    for t, j in enumerate(Lam):
        w = k2 + t
        for Q in lp[j]:
            edges.append((Q, w))
    return k2 + len(Lam), edges


def _run_pencils(d, D, rng, deadline, consider):
    q = _best_q(d)
    if q is None or q < 2:
        return
    s = d - q - 1
    m, pl, lp, base_edges = _incidence_lists(q)
    consider(2 * m, base_edges)  # plain PG(2,q): degree q+1 <= d, diameter 3
    if s < 1:
        return

    conic = _conic_seed(q)
    if s == 2:
        target = q + 1 if q % 2 == 1 else q + 2  # maximum arc sizes for s = 2
    else:
        target = 10 ** 9

    now = time.monotonic()
    half = (deadline - now) / 2
    Pi = _max_set(m, s, pl, lp, conic, target, rng, now + half)
    Lam = _max_set(m, s, lp, pl, conic, target, rng, time.monotonic() + half)
    if Pi or Lam:
        n, edges = _pencil_graph(m, pl, lp, base_edges, Pi, Lam)
        consider(n, edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        try:
            _run_pencils(d, D, rng, deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
