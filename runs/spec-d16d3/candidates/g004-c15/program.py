import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane data: points and lines are both indexed 0..m-1, the same
# vectors being used for both. Bitmasks give fast coverage tests.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, pl, lp, line_mask, point_mask) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]  # lines through point P
    lp = [[] for _ in range(m)]  # points on line L
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    line_mask = [sum(1 << p for p in lp[L]) for L in range(m)]
    point_mask = [sum(1 << L for L in pl[P]) for P in range(m)]
    return m, edges, pl, lp, line_mask, point_mask


def _conic(q):
    """Point indices of a conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


# ----------------------------------------------------------------------------
# NEW IDEA: pairwise-intersecting cover families.
#
# Attach a new vertex x on the point side, adjacent to a set T of lines that
# covers every point. Distance x..point is 2, x..line is <= 3, so the new
# vertex keeps diameter 3 with the PG base. Two such x, x' are at distance 2
# only if T and T' share a line, so the family must be pairwise intersecting.
# Each line gains one degree per family member containing it, capped at
# cap = d - (q+1). Points get new vertices by the dual construction, and the
# two families are independent. Stars at points are the classical case
# (the arc construction); this search also tries non-star covers of size
# <= d, which can allow more than q+1 members per side.
# ----------------------------------------------------------------------------

def _new_cover(masks, through, use, fam, cap, dmax, rng, seed_u, full):
    """Try to build one new cover: hits every family member, covers the universe, respects caps."""
    chosen, cset, covered = [], set(), 0
    order = list(range(len(fam)))
    rng.shuffle(order)
    for idx in order:
        T = fam[idx]
        if any(e in cset for e in T):
            continue
        avail = [e for e in T if use[e] < cap]
        if not avail:
            return None
        e = max(avail, key=lambda x: ((masks[x] & ~covered).bit_count(), rng.random()))
        chosen.append(e)
        cset.add(e)
        covered |= masks[e]
    if seed_u is not None:
        st = through[seed_u]
        if all(use[e] < cap for e in st):
            for e in st:
                if e not in cset:
                    chosen.append(e)
                    cset.add(e)
                    covered |= masks[e]
    if len(chosen) > dmax:
        return None
    while covered != full:
        if len(chosen) >= dmax:
            return None
        best, bg = -1, -1.0
        for e in range(len(masks)):
            if use[e] >= cap or e in cset:
                continue
            g = (masks[e] & ~covered).bit_count()
            if g == 0:
                continue
            sc = g + 0.5 * rng.random()
            if sc > bg:
                bg, best = sc, e
        if best < 0:
            return None
        chosen.append(best)
        cset.add(best)
        covered |= masks[best]
    return chosen


def _cover_family(m, masks, through, cap, dmax, rng, deadline):
    """Randomized restarts building a maximal pairwise-intersecting family of covers with use <= cap."""
    if cap < 1:
        return []
    full = (1 << m) - 1
    best = []
    while time.monotonic() < deadline:
        use = [0] * m
        fam, misses = [], 0
        while misses < 8 and time.monotonic() < deadline:
            seed_u = rng.randrange(m) if rng.random() < 0.8 else None
            T = _new_cover(masks, through, use, fam, cap, dmax, rng, seed_u, full)
            if T is None:
                misses += 1
                continue
            fam.append(T)
            for e in T:
                use[e] += 1
        if len(fam) > len(best):
            best = fam
    return best


def _family_graph(m, edges, X, Y):
    """PG incidence plus one point-side vertex per X cover and one line-side vertex per Y cover."""
    nX, nY = len(X), len(Y)
    n = 2 * m + nX + nY
    E = list(edges)
    for t, T in enumerate(X):
        x = 2 * m + t
        for L in T:
            E.append((x, m + L))
    for t, T in enumerate(Y):
        y = 2 * m + nX + t
        for P in T:
            E.append((P, y))
    return n, E


def _search_family(q, d, rng, deadline):
    """Return candidate (n, edges): the PG base, a conic-star baseline, and a searched family graph."""
    m, edges, pl, lp, line_mask, point_mask = _pg_data(q)
    out = [(2 * m, list(edges))]
    cap = d - q - 1
    if cap < 1:
        return out
    S = _conic(q)
    out.append(_family_graph(m, edges, [pl[P] for P in S], [lp[L] for L in S]))
    half = max(0.0, deadline - time.monotonic()) / 2
    X = _cover_family(m, line_mask, pl, cap, d, rng, time.monotonic() + half)
    Y = _cover_family(m, point_mask, lp, cap, d, rng, time.monotonic() + half)
    out.append(_family_graph(m, edges, X, Y))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit
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

    if D >= 3:
        qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)][:2]
        for i, q in enumerate(qs):
            now = time.monotonic()
            slot = max(0.0, end - now) / (len(qs) - i)
            for n_c, e_c in _search_family(q, d, rng, now + slot):
                consider(n_c, e_c)

    return best
