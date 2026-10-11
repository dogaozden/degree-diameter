import math
import random
import time

import lib

# New construction idea (not in the parent): a bi-Cayley / voltage-lift search over
# non-abelian groups, driven by hill-climbing on the number of vertex pairs at distance > D.
#
# Lift model: base has k "A" and k "B" vertices, and d darts (i, j, g) per base vertex on each
# side. The lift has vertices (A_i, x) and (B_j, x) for x in G, |G| = m, and edges
# (A_i, x) -- (B_j, x*g). It is bipartite, d-regular, and has n = 2*k*m vertices.
# Left translations are automorphisms, so the diameter condition reduces to 2k BFS runs,
# one from the identity of each class.
# Moves: change one voltage, or swap the B-endpoints of two darts. Both keep regularity.
# Groups: cyclic Z_m, or semidirect products Z_a x|_r Z_b with a*b = m.

_GROUP_CACHE = {}


def _group_options(m):
    """Return group descriptors of order m: ('c', m) or ('s', a, b, r) for Z_a x|_r Z_b."""
    if m in _GROUP_CACHE:
        return _GROUP_CACHE[m]
    opts = [("c", m)]
    for b in range(2, m):
        if m % b:
            continue
        a = m // b
        if a < 3:
            continue
        for r in range(2, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1:
                opts.append(("s", a, b, r))
    _GROUP_CACHE[m] = opts
    return opts


def _make_group(opt):
    if opt[0] == "c":
        _, mul, inv = lib.cyclic_group(opt[1])
    else:
        _, mul, inv = lib.semidirect_group(opt[1], opt[2], opt[3])
    return mul, inv


def _random_darts(k, d, m, rng):
    """Random d-regular base multigraph on k+k vertices with voltages; distinct (i, j, g) triples."""
    A = [i for i in range(k) for _ in range(d)]
    B = [j for j in range(k) for _ in range(d)]
    rng.shuffle(B)
    used = set()
    darts = []
    for i, j in zip(A, B):
        for _ in range(60):
            g = rng.randrange(m)
            if (i, j, g) not in used:
                break
        else:
            return None
        used.add((i, j, g))
        darts.append([i, j, g])
    return darts


def _propose(darts, rng, k, m):
    """Local move: change one voltage, or swap B-endpoints of two darts. None if it breaks distinctness."""
    new = [list(t) for t in darts]
    S = {tuple(t) for t in darts}
    if rng.random() < 0.6:
        p = rng.randrange(len(new))
        i, j, g = new[p]
        g2 = rng.randrange(m)
        if g2 == g or (i, j, g2) in S:
            return None
        new[p][2] = g2
    else:
        if len(new) < 2:
            return None
        p, q = rng.sample(range(len(new)), 2)
        i1, j1, g1 = new[p]
        i2, j2, g2 = new[q]
        if j1 == j2:
            return None
        if (i1, j2, g1) in S or (i2, j1, g2) in S:
            return None
        new[p] = [i1, j2, g1]
        new[q] = [i2, j1, g2]
    return new


def _bad_count(k, m, mul, inv_, darts, D):
    """Sum over the 2k class identities of the number of vertices NOT within distance D."""
    N = 2 * k * m
    out = [[] for _ in range(k)]
    inn = [[] for _ in range(k)]
    for i, j, g in darts:
        out[i].append((j, g))
        inn[j].append((i, inv_(g)))
    total = 0
    for c0 in range(2 * k):
        s = c0 * m
        seen = bytearray(N)
        seen[s] = 1
        frontier = [s]
        reached = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                c, x = divmod(v, m)
                if c < k:
                    for j, g in out[c]:
                        w = (k + j) * m + mul(x, g)
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    for i, gi in inn[c - k]:
                        w = i * m + mul(x, gi)
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += N - reached
    return total


def _attempt(k, m, d, D, rng, t_end):
    """One random restart plus hill-climb at (k, m). Return (n, edges) if a valid lift is found."""
    opt = rng.choice(_group_options(m))
    mul, inv_ = _make_group(opt)
    darts = _random_darts(k, d, m, rng)
    if darts is None:
        return None
    cur = _bad_count(k, m, mul, inv_, darts, D)
    while cur > 0 and time.monotonic() < t_end:
        new = _propose(darts, rng, k, m)
        if new is None:
            continue
        nc = _bad_count(k, m, mul, inv_, new, D)
        T = max(1.0, 0.02 * cur)
        if nc <= cur or rng.random() < math.exp(-(nc - cur) / T):
            darts, cur = new, nc
    if cur > 0:
        return None
    n = 2 * k * m
    edges = []
    for i, j, g in darts:
        for x in range(m):
            edges.append((i * m + x, (k + j) * m + mul(x, g)))
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Fallbacks, both valid for D >= 2.
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    best = lib.haar_graph(d, range(d))  # K_{d,d}
    best_N = best[0]

    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)
    ks = (1, 2, 3, 4, 6)
    try:
        while time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            slice_len = max(0.5, min(8.0, remaining / len(ks)))
            att = max(0.5, min(6.0, slice_len))
            for k in ks:
                now = time.monotonic()
                if now >= deadline:
                    break
                slice_end = min(deadline, now + slice_len)
                while time.monotonic() < slice_end:
                    m = max(d + 1, best_N // (2 * k) + 1)
                    res = _attempt(k, m, d, D, rng,
                                   min(slice_end, time.monotonic() + att))
                    if res is not None and res[0] > best_N:
                        best = res
                        best_N = res[0]
    except Exception:
        pass
    return best
