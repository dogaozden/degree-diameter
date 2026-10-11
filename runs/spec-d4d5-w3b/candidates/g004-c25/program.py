import math
import random
import time

import lib

_BIG = 10 ** 9
_GROUP_CACHE = {}


# ----------------------------------------------------------------------------
# Safe baselines (always valid for their D range).
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _k_dd(d):
    """K_{d,d}: diameter 2, degree d."""
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, searched by annealing
# with an all-pairs bitmask distance cost.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Layer L has k darts; dart idx = L*k + i joins A_{i,g} to B_{dj[idx], g*s}
# for every g, where s = sv[idx]. Within each layer dj is a permutation, so
# every A vertex and every B vertex has degree exactly d.
# ----------------------------------------------------------------------------

def _groups_of_order(G):
    """All (m, k2, r) with Z_m x| Z_k2 of order G (k2 <= 12). Cyclic group always included."""
    if G in _GROUP_CACHE:
        return _GROUP_CACHE[G]
    out = []
    for k2 in range(1, min(G, 12) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            rs = [1]
        else:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        for r in rs:
            out.append((m, k2, r))
    _GROUP_CACHE[G] = out
    return out


def _right_table(m, k2, r):
    """Return (order, R) with R[s][g] = g * s in the group."""
    order, mul, _ = lib.semidirect_group(m, k2, r)
    R = [[mul(g, s) for g in range(order)] for s in range(order)]
    return order, R


def _nbrs(k, G, R, dj, sv, d):
    N = 2 * k * G
    nbrs = [[] for _ in range(N)]
    for idx in range(d * k):
        i = idx % k
        base_a = i * G
        base_b = (k + dj[idx]) * G
        Rs = R[sv[idx]]
        for g in range(G):
            a = base_a + g
            b = base_b + Rs[g]
            nbrs[a].append(b)
            nbrs[b].append(a)
    return N, nbrs


def _dupcount(k, dj, sv, d):
    """Number of darts whose (i, j, s) triple repeats an earlier one (would create parallel edges)."""
    seen = set()
    dup = 0
    for idx in range(d * k):
        key = (idx % k, dj[idx], sv[idx])
        if key in seen:
            dup += 1
        else:
            seen.add(key)
    return dup


def _bad_pairs(N, nbrs, D):
    """Ordered (vertex, vertex) pairs at distance > D (unreachable counts as bad)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in nbrs[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _cost(k, G, R, dj, sv, d, D):
    dup = _dupcount(k, dj, sv, d)
    N, nbrs = _nbrs(k, G, R, dj, sv, d)
    return _bad_pairs(N, nbrs, D) + 50 * dup


def _edges(k, G, R, dj, sv, d):
    E = set()
    for idx in range(d * k):
        i = idx % k
        Rs = R[sv[idx]]
        base_b = (k + dj[idx]) * G
        for g in range(G):
            E.add((i * G + g, base_b + Rs[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, R, rng, deadline, steps):
    """Simulated annealing over voltages and within-layer target permutations.

    Returns (dj, sv) with zero cost, or None.
    """
    dj, sv = [], []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            dj.append(p[i])
            sv.append(rng.randrange(G))

    cur = _cost(k, G, R, dj, sv, d, D)
    if cur == 0:
        return dj, sv
    T0 = max(3.0, 0.05 * cur)
    T1 = 0.3
    decay = (T1 / T0) ** (1.0 / max(1, steps))
    T = T0

    for _ in range(steps):
        if time.monotonic() > deadline:
            break
        T *= decay
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(d * k)
            old = sv[idx]
            new = rng.randrange(G)
            if new == old:
                continue
            sv[idx] = new
            c2 = _cost(k, G, R, dj, sv, d, D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
                if cur == 0:
                    return dj, sv
            else:
                sv[idx] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            dj[ia], dj[ib] = dj[ib], dj[ia]
            c2 = _cost(k, G, R, dj, sv, d, D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
                if cur == 0:
                    return dj, sv
            else:
                dj[ia], dj[ib] = dj[ib], dj[ia]
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Exact optimum for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe baseline: K_{d,d} (valid for D >= 2), upgraded to PG(2,q) when D >= 3.
    best = _k_dd(d)
    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    # Diameter 2 bipartite: K_{d,d} is optimal.
    if D < 3:
        return best

    best_n = best[0]
    ks = [2, 3, 4, 5, 6, 7, 8]

    # Bi-Cayley lift search aimed at orders just above the current best.
    # Each success raises the target, so the search only moves upward.
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        target = best_n + 2
        G = -(-target // (2 * k)) + rng.randrange(0, 3)
        groups = _groups_of_order(G)
        if not groups:
            continue
        m, k2, r = rng.choice(groups)
        order, R = _right_table(m, k2, r)
        res = _anneal(d, D, k, order, R, rng, deadline, steps=1200)
        if res is None:
            continue
        dj, sv = res
        n, edges = _edges(k, order, R, dj, sv, d)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n

    if not lib.is_valid(best[0], best[1], d, D):
        best = _k_dd(d)
    return best
