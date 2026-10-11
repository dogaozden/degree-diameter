import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Voltage lifts over Z_m with several base vertices, found by simulated annealing.
#
# Base: bipartite multigraph with k vertices on side A (x = 0..k-1) and k on side B
# (y = k..2k-1), each vertex of degree d. Each base dart (x, y) carries a voltage a
# in Z_m. The lift has vertices (x, g), edges (x, g) ~ (y, g + a). It is d-regular,
# bipartite, and has 2k*m vertices.
#
# The lift is invariant under g -> g + t, so the diameter is <= D iff every base
# vertex x0 reaches all (x, g) within D steps from (x0, 0). Reachability is kept as
# bitmasks over Z_m, one per base vertex. Each cost evaluation is cheap.
#
# Calibration shortcuts (PG(2,q) incidence and Araujo-Lopez for D = 3) are kept.
# K_{d,d} is the always-valid fallback.
# ----------------------------------------------------------------------------


def _rot(X, a, m, full):
    """Shift the bitmask X by a (mod m): bit g moves to bit (g + a) mod m."""
    if a == 0:
        return X
    return ((X << a) | (X >> (m - a))) & full


def _cost(V, nb, m, D, full):
    """Total number of (base vertex, Z_m element) pairs NOT within D of (x0, 0), over all x0."""
    total = 0
    for x0 in range(V):
        R = [0] * V
        R[x0] = 1
        for _ in range(D):
            newR = list(R)
            for x in range(V):
                rx = R[x]
                if rx:
                    for y, a in nb[x]:
                        newR[y] |= _rot(rx, a, m, full)
            R = newR
        for x in range(V):
            total += m - R[x].bit_count()
    return total


def _eval(V, pairs, vol, m, D, full):
    nb = [[] for _ in range(V)]
    for (x, y), a in zip(pairs, vol):
        nb[x].append((y, a))
        nb[y].append((x, (m - a) % m))
    return _cost(V, nb, m, D, full)


def _base_pairs(k, d, rng):
    """k*d darts: each of the d rounds is a random perfect matching between the two sides."""
    pairs = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            pairs.append((i, k + perm[i]))
    return pairs


def _find_voltages(V, k, d, m, D, deadline, rng):
    """Anneal voltages (with random restarts of the base) until diameter <= D. Returns (pairs, vol) or None."""
    full = (1 << m) - 1
    while time.monotonic() < deadline:
        pairs = _base_pairs(k, d, rng)
        nd = len(pairs)
        groups = {}
        for i, p in enumerate(pairs):
            groups.setdefault(p, []).append(i)
        vol = [0] * nd
        for idxs in groups.values():
            # Parallel darts on one pair need distinct voltages (else duplicate edges).
            for i, a in zip(idxs, rng.sample(range(m), len(idxs))):
                vol[i] = a
        c = _eval(V, pairs, vol, m, D, full)
        best_c = c
        T = 1.0
        stall = 0
        while c > 0 and stall < 40000:
            if time.monotonic() > deadline:
                return None
            i = rng.randrange(nd)
            p = pairs[i]
            used = [vol[j] for j in groups[p] if j != i]
            b = rng.randrange(m)
            if b == vol[i] or b in used:
                stall += 1
                continue
            old = vol[i]
            vol[i] = b
            c2 = _eval(V, pairs, vol, m, D, full)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                c = c2
                if c < best_c:
                    best_c = c
                    stall = 0
                else:
                    stall += 1
            else:
                vol[i] = old
                stall += 1
            T = max(0.3, T * 0.9998)
        if c == 0:
            return pairs, vol
    return None


def _lift_edges(V, pairs, vol, m):
    edges = []
    for (x, y), a in zip(pairs, vol):
        for g in range(m):
            edges.append((x * m + g, y * m + (g + a) % m))
    return V * m, edges


def _lift_search(d, D, t_end, rng, floor_n):
    """Ladder over m for base sizes k = 2, 3, 1 (V = 2k). Returns best (n, edges) found, or None."""
    moore = lib._moore_bound(d, D)
    best = None
    best_n = floor_n
    fracs = {2: 0.5, 3: 0.6, 1: 1.0}
    for k in (2, 3, 1):
        now = time.monotonic()
        if now >= t_end:
            break
        V = 2 * k
        k_end = now + fracs[k] * (t_end - now)
        m = max(d, best_n // V + 1)
        while V * m <= moore and time.monotonic() < k_end:
            res = _find_voltages(V, k, d, m, D, k_end, rng)
            if res is None:
                break
            pairs, vol = res
            n, edges = _lift_edges(V, pairs, vol, m)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n = n
                best = (n, edges)
            m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Calibration shortcuts for D = 3.
    if D == 3:
        try:
            if d >= 3 and lib.is_prime_power(d - 1):
                n, e = lib.projective_plane_incidence(d - 1)
                consider(n, e)
        except Exception:
            pass
        try:
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
        except Exception:
            pass
        if best[0] >= moore:
            return best

    # Main construction: multi-vertex voltage lifts over Z_m.
    t_end = start + 0.85 * T
    try:
        cand = _lift_search(d, D, t_end, rng, best[0])
    except Exception:
        cand = None
    if cand is not None:
        consider(cand[0], cand[1])

    return best
