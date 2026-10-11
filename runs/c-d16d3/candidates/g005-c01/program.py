import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: general cover families on PG(2, q) (diameter 3, any D >= 3).
#
# Base: incidence graph of PG(2, q), points 0..m-1, lines m..2m-1. Old points
# have degree q+1 and so do old lines, leaving s = d-q-1 spare slots each.
#
# New A-vertices sit on the point side and join a set T of lines. New B-vertices
# sit on the line side and join a set of points. Validity needs only:
#   * every A covers all points with its lines (distance 2 to every point),
#   * any two A's share a line (distance 2), and dually for B's,
#   * each line is used by at most s A's, each point by at most s B's,
#   * |T| <= d for every new vertex.
# A-B distances are automatically <= 3, and old-old distances are unchanged.
#
# Pencils (all lines through a point) are the parent's special case. Here the
# search also tries arbitrary covers, chosen greedily so that they hit every
# existing set through a lightly loaded block, with random restarts.
# ----------------------------------------------------------------------------


def _masks(lists):
    """Bitmask of each list of small ints."""
    out = []
    for xs in lists:
        mm = 0
        for x in xs:
            mm |= 1 << x
        out.append(mm)
    return out


def _conic_centers(q):
    """Conic plus nucleus (q even) as indices into lib.projective_points(q)."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _seed(pen, centers, Bn, s, d):
    """Pencil family at the given centers if all block loads stay <= s, else []."""
    if not centers or any(len(pen[c]) > d for c in centers):
        return []
    load = [0] * Bn
    for c in centers:
        for b in pen[c]:
            load[b] += 1
    if max(load) > s:
        return []
    return [list(pen[c]) for c in centers]


def _pencil_greedy(pen, Bn, s, d, rng):
    """Random greedy family of pencils respecting block loads <= s."""
    order = list(range(len(pen)))
    rng.shuffle(order)
    load = [0] * Bn
    sets = []
    for c in order:
        blocks = pen[c]
        if len(blocks) > d or any(load[b] >= s for b in blocks):
            continue
        for b in blocks:
            load[b] += 1
        sets.append(list(blocks))
    return sets


def _state(sets, Bn):
    """Block loads and, per block, the bitmask of sets containing it."""
    load = [0] * Bn
    setmask = [0] * Bn
    for k, T in enumerate(sets):
        bit = 1 << k
        for b in T:
            load[b] += 1
            setmask[b] |= bit
    return load, setmask


def _attempt(mem, U, Bn, load, setmask, nsets, s, d, rng):
    """Greedy randomized cover that also hits every existing set. Returns block list or None."""
    full = (1 << U) - 1
    allhit = (1 << nsets) - 1
    covered = 0
    hit = 0
    chosen = []
    chosen_set = set()
    noise = 1.0 + rng.random()
    while covered != full or hit != allhit:
        if len(chosen) >= d:
            return None
        best = -1
        bestsc = -1.0
        for b in range(Bn):
            if load[b] >= s or b in chosen_set:
                continue
            g = (mem[b] & ~covered).bit_count() + (setmask[b] & ~hit).bit_count()
            if g == 0:
                continue
            sc = g + rng.random() * noise
            if sc > bestsc:
                bestsc = sc
                best = b
        if best < 0:
            return None
        chosen.append(best)
        chosen_set.add(best)
        covered |= mem[best]
        hit |= setmask[best]
    return chosen


def _grow(init, mem, U, Bn, s, d, rng, deadline, tries):
    """Extend a valid family by general covers until attempts fail or time runs out."""
    sets = [list(T) for T in init]
    load, setmask = _state(sets, Bn)
    while time.monotonic() < deadline:
        added = False
        for _ in range(tries):
            T = _attempt(mem, U, Bn, load, setmask, len(sets), s, d, rng)
            if T is not None:
                k = len(sets)
                bit = 1 << k
                for b in T:
                    load[b] += 1
                    setmask[b] |= bit
                sets.append(T)
                added = True
                break
        if not added:
            break
    return sets


def _best_side(mem, pen, U, Bn, s, d, rng, deadline, seed_sets):
    """Restarts of greedy family building for one side; returns the largest valid family."""
    best = [list(T) for T in seed_sets]
    while time.monotonic() < deadline:
        r = rng.random()
        if seed_sets and r < 0.3:
            init = [list(T) for T in seed_sets]
        elif r < 0.65:
            init = _pencil_greedy(pen, Bn, s, d, rng)
        else:
            init = []
        sets = _grow(init, mem, U, Bn, s, d, rng, deadline, 16)
        if len(sets) > len(best):
            best = sets
    return best


def _construct(q, d, rng, deadline):
    """Build the PG(2,q)-based graph with cover families on both sides; returns (n, edges) or None."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    s = d - q - 1
    if s < 0:
        return None
    pl = [[] for _ in range(m)]   # lines through each point
    lp = [[] for _ in range(m)]   # points on each line
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)

    centers = _conic_centers(q)
    now = time.monotonic()
    mid = now + (deadline - now) / 2
    seedA = _seed(pl, centers, m, s, d)
    seedB = _seed(lp, centers, m, s, d)

    # A side: universe = points, blocks = lines (A-vertices on point side).
    A = _best_side(_masks(lp), pl, m, m, s, d, rng, mid, seedA)
    # B side: universe = lines, blocks = points (dual).
    B = _best_side(_masks(pl), lp, m, m, s, d, rng, deadline, seedB)

    kA, kB = len(A), len(B)
    E = list(edges)
    for t, T in enumerate(A):
        x = 2 * m + t
        for L in T:
            E.append((x, m + L))
    for t, T in enumerate(B):
        x = 2 * m + kA + t
        for P in T:
            E.append((P, x))
    return 2 * m + kA + kB, E


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.6 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best

    best_n = best[0]
    rng = random.Random(seed * 1000003 + 97 * d + D)
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)),
                reverse=True)

    def weight(q):
        return q * q + q + 1

    for i, q in enumerate(qs):
        now = time.monotonic()
        left = max(0.0, deadline - now)
        wsum = sum(weight(x) for x in qs[i:])
        q_deadline = now + left * weight(q) / wsum
        try:
            cand = _construct(q, d, rng, q_deadline)
        except Exception:
            cand = None
        if cand is not None and cand[0] > best_n and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
            best_n = cand[0]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
