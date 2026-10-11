import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products Z_m x|_r Z_k, searched by
# simulated annealing with a vectorised BFS cost.
#
# Model: k base vertices A_0..A_{k-1} and k base vertices B_0..B_{k-1}, each
# with d layers. Layer L pairs A_i with B_{p_L(i)} through a voltage g_{L,i}
# in G, where p_L is a permutation of range(k). The lift has vertices
# A(i,x) and B(j,y) for x, y in G, and edges A(i,x) -- B(p_L(i), x*g_{L,i}).
# Every vertex has degree d, the graph is bipartite, and left multiplication
# by G is an automorphism. Hence checking distances from A(i,e) and B(j,e)
# is enough for the whole graph.
#
# Cost = number of (source, vertex) pairs at distance > D. Zero means valid.
# Anything found is re-checked with lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _groups(G):
    """Semidirect parameters (m, k2, r) with m * k2 = G."""
    out = []
    for k2 in _divisors(G):
        m = G // k2
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


def _tables(m, k2, r):
    """Cached (G, C, Cinv): C[h, y] = y*h and Cinv[g] = C[g^-1] as numpy arrays."""
    key = (m, k2, r)
    hit = _GROUP_CACHE.get(key)
    if hit is not None:
        return hit
    G, mul, inv = lib.semidirect_group(m, k2, r)
    C = np.empty((G, G), dtype=np.int64)
    for h in range(G):
        for y in range(G):
            C[h, y] = mul(y, h)
    invs = np.array([inv(g) for g in range(G)], dtype=np.int64)
    Cinv = C[invs]
    val = (G, C, Cinv)
    if len(_GROUP_CACHE) >= 24:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[key] = val
    return val


def _neighbours(k, G, C, Cinv, d, perms, volts):
    """Neighbour matrix nb[v, L] of the lift; A-vertices are 0..kG-1, B-vertices kG..2kG-1."""
    n = 2 * k * G
    nb = np.empty((n, d), dtype=np.int64)
    for L in range(d):
        pl = perms[L]
        vl = volts[L]
        for i in range(k):
            p = pl[i]
            g = vl[i]
            nb[i * G:(i + 1) * G, L] = (k + p) * G + C[g]
            nb[(k + p) * G:(k + p + 1) * G, L] = i * G + Cinv[g]
    return nb


def _cost(k, G, D, d, perms, volts, C, Cinv):
    """Unreached (source, vertex) pairs within distance D, over the 2k base sources."""
    nb = _neighbours(k, G, C, Cinv, d, perms, volts)
    n = 2 * k * G
    sources = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in sources:
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        count = 1
        for _ in range(D):
            cand = nb[frontier].ravel()
            cand = cand[~seen[cand]]
            if cand.size == 0:
                break
            cand = np.unique(cand)
            seen[cand] = True
            count += int(cand.size)
            frontier = cand
        total += n - count
    return total


def _ok_col(d, perms, volts, i):
    """No duplicate edge: pairs (p_L(i), g_{L,i}) must be distinct over layers L."""
    seen = set()
    for L in range(d):
        key = (perms[L][i], volts[L][i])
        if key in seen:
            return False
        seen.add(key)
    return True


def _anneal(d, D, k, G, C, Cinv, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns (perms, volts) or None."""
    perms = volts = None
    for _ in range(100):
        perms = [rng.sample(range(k), k) for _ in range(d)]
        volts = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
        if all(_ok_col(d, perms, volts, i) for i in range(k)):
            break
    else:
        return None

    cost = _cost(k, G, D, d, perms, volts, C, Cinv)
    T0, T1 = 2.0, 0.15
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))

        if k > 1 and rng.random() < 0.25:
            # Swap two B-targets inside one layer (keeps p_L a permutation).
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            pl = perms[L]
            pl[a], pl[b] = pl[b], pl[a]
            if not all(_ok_col(d, perms, volts, i) for i in range(k)):
                pl[a], pl[b] = pl[b], pl[a]
                continue
            c2 = _cost(k, G, D, d, perms, volts, C, Cinv)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
            else:
                pl[a], pl[b] = pl[b], pl[a]
        else:
            # Change one voltage.
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = volts[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volts[L][i] = new
            if not _ok_col(d, perms, volts, i):
                volts[L][i] = old
                continue
            c2 = _cost(k, G, D, d, perms, volts, C, Cinv)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
            else:
                volts[L][i] = old

    if cost == 0:
        return perms, volts
    return None


def _search(d, D, best, deadline, rng):
    """Search for valid lifts with more vertices than best; returns the best validated graph."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        n_best = best[0]
        ks = [kk for kk in (1, 2, 3)
              if 2 * kk * (n_best // (2 * kk) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        lo = n_best // (2 * k) + 1
        spread = max(1, lo // 12)
        G = lo + rng.randrange(spread)
        if 2 * k * G > moore:
            G = lo
        groups = _groups(G)
        if not groups:
            continue
        m, k2, r = rng.choice(groups)
        G2, C, Cinv = _tables(m, k2, r)
        slice_end = min(deadline, time.monotonic() + 2.5)
        res = _anneal(d, D, k, G2, C, Cinv, rng, slice_end, 4000)
        if res is not None:
            perms, volts = res
            n = 2 * k * G2
            nb = _neighbours(k, G2, C, Cinv, d, perms, volts)
            edges = [(a, int(b)) for a in range(k * G2) for b in nb[a]]
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # D = 3 with d-1 a prime power: projective plane incidence meets the Moore bound.
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
        if best[0] >= moore:
            return best

    try:
        best = _search(d, D, best, deadline, rng)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
