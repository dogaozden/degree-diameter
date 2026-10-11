import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: Z_m voltage lifts of small bipartite base multigraphs.
#
# Base graph: p black vertices A_i and p white vertices B_j, with d darts per
# base vertex, so the base is d-regular bipartite (built from d random
# permutations of range(p)). Each dart (i, j, a) joins (A_i, x) to (B_j, x+a).
# The lift has 2*p*m vertices, is d-regular and bipartite, and is invariant
# under Z_m translation.
#
# Diameter check: by translation invariance it suffices to take each base
# vertex as a source at offset 0 and check that every fiber is covered within D
# steps. Balls are kept as m-bit masks per base vertex, so one check costs
# O(p^2 * D * d) bitmask rotations. Simulated annealing adjusts the voltages
# (keeping voltages distinct within each parallel class) to drive the number of
# unreached (source, target) pairs to zero.
# ----------------------------------------------------------------------------


def _rot(M, s, m, full):
    """Bitmask M with every element y moved to (y + s) mod m."""
    if s == 0:
        return M
    return ((M << s) | (M >> (m - s))) & full


def _cost(p, darts, m, full, D):
    """Number of (source base vertex, target vertex) pairs not within distance D."""
    B = 2 * p
    adjl = [[] for _ in range(B)]
    for i, j, a in darts:
        adjl[i].append((p + j, (-a) % m))   # {x : x + a in M_j} = rot(M_j, -a)
        adjl[p + j].append((i, a % m))      # {x : x - a in M_i} = rot(M_i, a)
    total = 0
    for src in range(B):
        M = [0] * B
        M[src] = 1
        for _ in range(D):
            new = [0] * B
            for v in range(B):
                x = M[v]
                for u, s in adjl[v]:
                    x |= _rot(M[u], s, m, full)
                new[v] = x
            M = new
        for x in M:
            total += m - x.bit_count()
    return total


def _search(p, d, m, deadline, rng, D):
    """Find voltages for a p-per-side, d-regular base lifted over Z_m with diameter <= D.

    Returns a list of darts (i, j, a) or None if the deadline passes first.
    """
    if m < d:
        return None
    full = (1 << m) - 1
    while time.monotonic() < deadline:
        # Fresh random base structure: d random permutations of range(p).
        pairs = []
        for _ in range(d):
            s = list(range(p))
            rng.shuffle(s)
            pairs.extend((i, s[i]) for i in range(p))
        K = len(pairs)
        groups = {}
        for k, key in enumerate(pairs):
            groups.setdefault(key, []).append(k)
        if any(len(ks) > m for ks in groups.values()):
            return None
        volt = [0] * K
        for ks in groups.values():
            for k, a in zip(ks, rng.sample(range(m), len(ks))):
                volt[k] = a

        def darts_of():
            return [(pairs[k][0], pairs[k][1], volt[k]) for k in range(K)]

        c = _cost(p, darts_of(), m, full, D)
        best_c = c
        last = 0
        it = 0
        T = 2.0
        while c > 0 and it - last < 4000:
            it += 1
            if it % 64 == 0 and time.monotonic() > deadline:
                return None
            k = rng.randrange(K)
            ks = groups[pairs[k]]
            a = rng.randrange(m)
            if any(volt[k2] == a for k2 in ks):
                continue
            old = volt[k]
            volt[k] = a
            c2 = _cost(p, darts_of(), m, full, D)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                c = c2
                if c < best_c:
                    best_c = c
                    last = it
            else:
                volt[k] = old
            T = max(0.2, T * 0.9995)
        if c == 0:
            return darts_of()
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.82 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Round-robin over base sizes p. For each p, target the smallest m that
    # would beat the current best. Give slices longer when a p keeps failing.
    ps = [2, 3, 1, 4]
    fails = {p: 0 for p in ps}
    while time.monotonic() < deadline:
        for p in ps:
            if time.monotonic() >= deadline:
                break
            m = max(d, best[0] // (2 * p) + 1)
            if 2 * p * m > moore:
                continue
            base = max(0.6, 0.06 * T)
            slice_len = min(0.35 * T, base * (1 + 0.5 * fails[p]))
            end = min(deadline, time.monotonic() + slice_len)
            try:
                darts = _search(p, d, m, end, rng, D)
            except Exception:
                darts = None
            if darts is None:
                fails[p] += 1
                continue
            fails[p] = 0
            n_new, e_new = lib.voltage_lift(
                2 * p, [(i, p + j, a) for i, j, a in darts], m)
            consider(n_new, e_new)
            if best[0] >= moore:
                return best

    return best
