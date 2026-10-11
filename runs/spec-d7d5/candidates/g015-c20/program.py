import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact small constructions (calibration-style cases).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: single-base-edge bi-Cayley (Haar-type) graphs over
# semidirect products G = Z_m x| Z_k2, with |G| = order chosen near the record.
#
# Vertices: A_g = g, B_h = G + h for g, h in G.
# Voltage set S = {s_0, ..., s_{d-1}} of d DISTINCT group elements:
#   A_g ~ B_{g*s}  for every s in S.
# Left multiplication by x is an automorphism (x*g)*s = x*(g*s), so distances
# from the two representatives A_identity and B_identity cover all orbits.
# Degree is exactly d because S is a set of distinct elements.
#
# Search: for a fixed order G, sample groups and run simulated annealing on the
# voltage set, minimising the number of (representative, vertex) pairs left
# farther than D. Orders are scanned upward; each success is kept and the scan
# moves on to the next order.
# ----------------------------------------------------------------------------

_SLICE = 2.0       # seconds spent on each order before moving on
_ITERS = 1500      # annealing steps per attempt


def _groups_of_order(G, rng):
    """All semidirect products Z_m x| Z_k2 with m*k2 = G (m >= 2), as (m, k2, r) triples."""
    groups = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            groups.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                groups.append((m, k2, r))
    rng.shuffle(groups)
    return groups


def _tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _cost(G, D, nbr):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    N = 2 * G
    reach = np.zeros(N, dtype=np.int64)
    reach[0] = 1       # representative A_identity
    reach[G] = 2       # representative B_identity
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[0]):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    pop = (reach & 1) + ((reach >> 1) & 1)
    return 2 * N - int(pop.sum())


def _fill_row(nbr, l, s, G, Ts, Invs):
    nbr[l, :G] = G + Ts[s]
    nbr[l, G:] = Invs[s]


def _climb(d, D, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over d distinct voltages. Returns the voltage list or None."""
    S = rng.sample(range(G), d)
    nbr = np.empty((d, 2 * G), dtype=np.int64)
    for l, s in enumerate(S):
        _fill_row(nbr, l, s, G, Ts, Invs)
    cost = _cost(G, D, nbr)
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.05 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[l]
        S[l] = new
        _fill_row(nbr, l, new, G, Ts, Invs)
        c2 = _cost(G, D, nbr)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l] = old
            _fill_row(nbr, l, old, G, Ts, Invs)
    return list(S) if cost == 0 else None


def _try_order(G, d, D, rng, slice_end):
    """Try to find a valid voltage set for order G before slice_end. Returns (n, edges) or None."""
    groups = _groups_of_order(G, rng)
    if not groups:
        return None
    idx = 0
    while time.monotonic() < slice_end:
        m, k2, r = groups[idx % len(groups)]
        idx += 1
        Gg, Ts, Invs = _tables(m, k2, r)
        S = _climb(d, D, Gg, Ts, Invs, rng, slice_end, _ITERS)
        if S is not None:
            edges = []
            for s in S:
                for g in range(Gg):
                    edges.append((g, Gg + int(Ts[s, g])))
            return 2 * Gg, edges
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best, best_n = pg, pg[0]
        if lib.is_prime_power(d - 1):
            return best

    try:
        moore = lib._moore_bound(d, D)
        # Start well below the expected frontier (easy orders succeed quickly),
        # then scan upward toward and beyond the record.
        G = max(best_n // 2 + 1, max(d, int(0.3 * moore / 2)))
        while time.monotonic() < deadline:
            slice_end = min(deadline, time.monotonic() + _SLICE)
            res = _try_order(G, d, D, rng, slice_end)
            if res is not None:
                n, edges = res
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best, best_n = (n, edges), n
            G += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
