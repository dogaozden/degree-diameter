import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base and small helpers.
# ----------------------------------------------------------------------------

def _prime_power_list(top, bottom=2):
    """Prime powers q with bottom <= q <= top, largest first."""
    return [q for q in range(top, bottom - 1, -1) if lib.is_prime_power(q)]


def _plane(q):
    """PG(2,q) incidence data: m points, m lines, base edges, point->lines, line->points."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]   # pl[P] = lines through point P
    lp = [[] for _ in range(m)]   # lp[L] = points on line L
    for u, v in edges:
        L = v - m
        pl[u].append(L)
        lp[L].append(u)
    return m, edges, pl, lp


def _conic(q):
    """Conic (plus nucleus for even q) as a set of vector indices, i.e. a 2-per-line arc.

    Points and lines share the same vector indexing, and the incidence is the dot
    product, so this set is also a 2-per-point family of lines.
    """
    pts = lib.projective_points(q)
    idx = {v: i for i, v in enumerate(pts)}
    F = lib.GF(q)
    S = [idx[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(idx[(0, 0, 1)])
    if q % 2 == 0:
        S.append(idx[(0, 1, 0)])
    return S


# ----------------------------------------------------------------------------
# NEW: independent capacitated packing on each side.
#
# Base PG(2,q) with spare s = d - (q+1) per vertex. Add two independent families:
#   X-vertices: one per chosen point P, joined to the q+1 lines through P.
#   Y-vertices: one per chosen line L, joined to the q+1 points on L.
# Capacity: each line holds <= s chosen points, each point lies on <= s chosen
# lines. The two families are chosen independently (the parent coupled them
# via one shared set). Any such choice keeps diameter 3, because every pair on
# the same side shares a block and every cross pair is within distance 3.
# ----------------------------------------------------------------------------

def _local(cover, nelem, s, init, rng, deadline):
    """Feasible set S of candidates (each covering the elements in cover[c]),
    each element covered <= s times, found by greedy start + plateau/swap search."""
    m = len(cover)
    cset = [frozenset(c) for c in cover]
    load = [0] * nelem
    inS = [False] * m
    S = []

    def add(c):
        inS[c] = True
        S.append(c)
        for e in cover[c]:
            load[e] += 1

    def remove(c):
        inS[c] = False
        S.remove(c)
        for e in cover[c]:
            load[e] -= 1

    for c in init:
        if not inS[c] and all(load[e] < s for e in cover[c]):
            add(c)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        c = rng.randrange(m)
        if inS[c]:
            continue
        sat = {e for e in cover[c] if load[e] >= s}
        if sat:
            # Members of S whose cover meets a saturated element of c block c.
            B = [r for r in S if not cset[r].isdisjoint(sat)]
            if len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
                for r in B:
                    remove(r)
                add(c)  # feasible: every saturated element is now empty
            else:
                continue
        else:
            add(c)
        if len(S) > len(best):
            best = list(S)
    return best


def _best_side(cover, nelem, s, conic, rng, deadline):
    """Best packing for one side, from two starts (conic order, random order)."""
    m = len(cover)
    if s <= 0 or m == 0:
        return []
    start = time.monotonic()
    budget = max(0.0, deadline - start)
    order = list(range(m))
    rng.shuffle(order)
    inits = [order]
    if conic is not None:
        inits.insert(0, conic)
    best = []
    for k, init in enumerate(inits):
        dl = start + budget * (k + 1) / len(inits)
        res = _local(cover, nelem, s, init, rng, dl)
        if len(res) > len(best):
            best = res
    return best


def _assemble(m, base_edges, pl, lp, S1, S2):
    """Base PG incidence plus X-vertices (points in S1) and Y-vertices (lines in S2)."""
    n = 2 * m + len(S1) + len(S2)
    E = list(base_edges)
    for t, P in enumerate(S1):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    off = 2 * m + len(S1)
    for t, L in enumerate(S2):
        y = off + t
        for P in lp[L]:
            E.append((P, y))
    return n, E


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Cycle C_{2D} for d = 2: bipartite, degree 2, diameter D.
    if d == 2 and D >= 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])

    if D >= 3:
        qs = _prime_power_list(min(d - 1, 40))
        if qs:
            # Plain projective plane: diameter 3, degree q+1 <= d.
            q0 = qs[0]
            n0, e0 = lib.projective_plane_incidence(q0)
            consider(n0, e0)

            # Independent X/Y packings on the largest few planes with spare capacity.
            cands = [q for q in qs if d - q - 1 >= 1][:4]
            for idx, q in enumerate(cands):
                now = time.monotonic()
                if now > deadline:
                    break
                share = (deadline - now) / (len(cands) - idx)
                m, edges, pl, lp = _plane(q)
                s = d - q - 1
                conic = _conic(q)
                S1 = _best_side(pl, m, s, conic, rng, now + share * 0.5)
                S2 = _best_side(lp, m, s, conic, rng, now + share)
                n, e = _assemble(m, edges, pl, lp, S1, S2)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
