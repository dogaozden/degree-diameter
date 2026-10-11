import random
import time

import lib


# ----------------------------------------------------------------------------
# Diameter-3 construction: PG(2,q) incidence plus two families of extra vertices.
#
# Point-side vertex x_i is joined to a set C_i of lines. Line-side vertex y_i is
# joined to the same index set C_i read as points (the plane is self-dual under
# the index identification). Requirements, all met by the family rules below:
#   * every C_i covers all points (so x_i is at distance <= 2 from every point),
#   * every C_i meets every C_j (so x_i, x_j and y_i, y_j are at distance 2),
#   * every line used by a C_i carries at most s = d - q - 1 extra edges.
# Then x_i and y_j are at distance <= 3 automatically. The order is
# 2(q^2+q+1) + 2a, where a is the family size.
# ----------------------------------------------------------------------------


def _prime_powers_desc(limit):
    return [q for q in range(limit, 1, -1) if lib.is_prime_power(q)]


def _line_masks(q):
    """Return (m, lmask, edges): lmask[L] is the bitmask of points on line L."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    lmask = [0] * m
    for u, v in edges:
        lmask[v - m] |= 1 << u
    return m, lmask, edges


def _conic_family(q, m, lmask, s):
    """Pencils at the q+1 points of a conic (odd q): pairwise intersecting, load <= 2."""
    if q % 2 == 0:
        return []
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    cone = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    fam = [frozenset(L for L in range(m) if (lmask[L] >> index[v]) & 1) for v in cone]
    load = [0] * m
    for f in fam:
        for L in f:
            load[L] += 1
    if max(load) > s:
        return []
    return fam


def _rand_cover(m, s, d, lmask, full, load, owners, nf, rng):
    """Randomized greedy: cover all points with <= d lines of load < s, hitting every existing family."""
    covered = 0
    cover = []
    cs = set()
    unhit = set(range(nf))
    while True:
        if covered == full and not unhit:
            return cover
        if len(cover) >= d:
            return None
        need = covered != full
        best_sc, best_L = -1.0, -1
        for L in range(m):
            if load[L] >= s or L in cs:
                continue
            h = 0
            for i in owners[L]:
                if i in unhit:
                    h += 1
            g = (lmask[L] & ~covered).bit_count() if need else 0
            if g == 0 and h == 0:
                continue
            sc = 2.0 * g + 4.0 * h + rng.random()
            if sc > best_sc:
                best_sc, best_L = sc, L
        if best_L < 0:
            return None
        cover.append(best_L)
        cs.add(best_L)
        covered |= lmask[best_L]
        for i in owners[best_L]:
            unhit.discard(i)


def _family_search(m, s, d, lmask, full, rng, deadline, init):
    """Grow a pairwise-intersecting family of covers; drop a random member after repeated failures."""
    fams = list(init)
    best = list(fams)
    fails = 0
    while time.monotonic() < deadline:
        load = [0] * m
        owners = [[] for _ in range(m)]
        for i, f in enumerate(fams):
            for L in f:
                load[L] += 1
                owners[L].append(i)
        cov = _rand_cover(m, s, d, lmask, full, load, owners, len(fams), rng)
        if cov is not None:
            fams.append(frozenset(cov))
            fails = 0
            if len(fams) > len(best):
                best = list(fams)
        else:
            fails += 1
            if fails > 400 and fams:
                fams.pop(rng.randrange(len(fams)))
                fails = 0
    return best


def _family_graph(m, edges, fam):
    """PG(2,q) incidence plus x_i (point side) and y_i (line side) for each family member."""
    a = len(fam)
    n = 2 * m + 2 * a
    E = list(edges)
    for i, f in enumerate(fam):
        x = 2 * m + i
        for L in f:
            E.append((x, m + L))
        y = 2 * m + a + i
        for P in f:
            E.append((P, y))
    return n, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        qs = _prime_powers_desc(d - 1)[:2]
        for idx, q in enumerate(qs):
            n_pg, e_pg = lib.projective_plane_incidence(q)
            consider(n_pg, e_pg)
            s = d - q - 1
            if s < 1:
                continue
            m, lmask, edges = _line_masks(q)
            full = (1 << m) - 1
            now = time.monotonic()
            slice_ = max(0.0, end - now) / (len(qs) - idx)
            # Half the slice: search seeded with the conic family (guarantees the parent's order).
            seeded = _conic_family(q, m, lmask, s)
            fam_a = _family_search(m, s, d, lmask, full, rng, now + slice_ / 2, seeded)
            # Other half: search from scratch, which may find non-pencil families.
            fam_b = _family_search(m, s, d, lmask, full, rng, now + slice_, [])
            fam = fam_a if len(fam_a) >= len(fam_b) else fam_b
            if fam:
                n, e = _family_graph(m, edges, fam)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
