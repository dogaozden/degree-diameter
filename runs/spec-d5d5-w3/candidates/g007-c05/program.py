import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy for this version:
#   * Safe fallbacks: K_{d,d} (diameter 2), cycles for d = 2, and the Heawood /
#     projective-plane incidence graph for D = 3 when d-1 is a prime power.
#   * Main engine (new, different from the earlier hill-climb): simulated
#     annealing over ABELIAN voltage lifts with k base vertices per side and
#     cyclic group Z_G. The lift is 2*k*G vertices with degree d. Distances are
#     computed with big-int bitmasks, where a group translation is a cyclic
#     bit rotation, so each cost evaluation is cheap.
#   * Every candidate is checked with lib.is_valid before it replaces the best.
# ----------------------------------------------------------------------------


def _k_dim_fallback(d):
    """K_{d,d}: 2d vertices, bipartite, diameter 2."""
    return lib.haar_graph(d, range(d))


def _rot(x, s, G, full):
    """Bitmask of {y + s mod G : y in x}; x is a subset of Z_G stored as bits."""
    return ((x << s) | (x >> (G - s))) & full


def _cost(k, G, D, full, darts):
    """Number of (source, vertex) pairs not within distance D.

    Sources are A_{i,0} and B_{j,0} for every orbit. Zero means the lift has diameter <= D.
    Dart (i, j, s) joins A_{i,x} to B_{j,x+s} for all x in Z_G.
    """
    N2 = 2 * k * G
    total = 0
    sources = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    # Precompute the negated shift for the B -> A direction.
    neg = [((G - s) % G) for _, _, s in darts]
    for side, idx in sources:
        RA = [0] * k
        RB = [0] * k
        if side == 0:
            RA[idx] = 1
        else:
            RB[idx] = 1
        for _ in range(D):
            nRA = RA[:]
            nRB = RB[:]
            for t, (i, j, s) in enumerate(darts):
                x = RA[i]
                if x:
                    nRB[j] |= ((x << s) | (x >> (G - s))) & full
                y = RB[j]
                if y:
                    sn = neg[t]
                    nRA[i] |= ((y << sn) | (y >> (G - sn))) & full
            RA, RB = nRA, nRB
        reached = 0
        for x in RA:
            reached += x.bit_count()
        for x in RB:
            reached += x.bit_count()
        total += N2 - reached
    return total


def _lift_edges(k, G, darts):
    """Edges and vertex count of the abelian lift described by darts."""
    E = []
    for i, j, s in darts:
        for x in range(G):
            E.append((i * G + x, k * G + j * G + (x + s) % G))
    return 2 * k * G, E


def _sa_chain(d, D, k, G, rng, stop, iters):
    """One simulated-annealing run. Returns a dart list (i, j, s) of zero cost, or None."""
    full = (1 << G) - 1
    perms = []
    shifts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        perms.append(p)
        shifts.append([rng.randrange(G) for _ in range(k)])

    def darts_now():
        return [(i, perms[L][i], shifts[L][i]) for L in range(d) for i in range(k)]

    ds = darts_now()
    tries = 0
    while len(set(ds)) < len(ds):
        tries += 1
        if tries > 200:
            return None
        L = rng.randrange(d)
        i = rng.randrange(k)
        shifts[L][i] = rng.randrange(G)
        ds = darts_now()

    cost = _cost(k, G, D, full, ds)
    T0, T1 = 3.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > stop:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        if k == 1 or rng.random() < 0.7:
            # Move: change one shift.
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = shifts[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            shifts[L][i] = new
            ds = darts_now()
            if len(set(ds)) < len(ds):
                shifts[L][i] = old
                continue
            c2 = _cost(k, G, D, full, ds)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
            else:
                shifts[L][i] = old
        else:
            # Move: swap the B-endpoints of two darts within one layer.
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            p = perms[L]
            p[a], p[b] = p[b], p[a]
            ds = darts_now()
            if len(set(ds)) < len(ds):
                p[a], p[b] = p[b], p[a]
                continue
            c2 = _cost(k, G, D, full, ds)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
            else:
                p[a], p[b] = p[b], p[a]

    if cost == 0:
        return darts_now()
    return None


def _search(d, D, k, G, rng, stop, chain_iters=20000):
    """Repeated annealing chains for one (k, G) until stop. Returns darts or None."""
    while time.monotonic() < stop:
        darts = _sa_chain(d, D, k, G, rng, stop, chain_iters)
        if darts is not None:
            return darts
    return None


def _cycle_graph(n):
    """Cycle C_n (n even for bipartiteness)."""
    return n, sorted({(min(i, (i + 1) % n), max(i, (i + 1) % n)) for i in range(n)})


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return _k_dim_fallback(d)
    if d == 2:
        return _cycle_graph(2 * D)

    moore = lib.moore_bound(d, D)
    best = _k_dim_fallback(d)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baseline for D = 3: incidence graph of PG(2, d-1) when d-1 is a prime power.
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        consider(n0, e0)

    rng = random.Random(seed * 1000003 + d * 97 + D)

    # Main search: abelian multi-orbit voltage lifts, cycling through k = 1, 2, 3.
    k_cycle = (1, 2, 3)
    t_idx = 0
    while time.monotonic() < deadline and best[0] < moore:
        k = k_cycle[t_idx % len(k_cycle)]
        t_idx += 1
        best_n = best[0]
        lo = best_n // (2 * k) + 1
        hi = moore // (2 * k)
        if lo > hi:
            continue
        G = lo + rng.randrange(min(4, hi - lo + 1))
        if G < d:
            continue
        remaining = deadline - time.monotonic()
        if remaining < 0.2:
            break
        chain_stop = time.monotonic() + min(6.0, remaining)
        darts = _search(d, D, k, G, rng, min(chain_stop, deadline))
        if darts is not None:
            n, E = _lift_edges(k, G, darts)
            consider(n, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _k_dim_fallback(d)
    return best
