"""Bi-Cayley voltage lifts grown by orbit insertion.

New idea (not in the parent): instead of restarting from scratch for every
base size, a lift over a fixed group G is grown one base block at a time.
Given a valid base multigraph on K+1 blocks per side, a new orbit pair
(A_K, B_K) of 2G vertices is inserted by removing t = d - y darts (i, j, s)
from the old base and adding (i, K), (K, j) for each removed dart plus y
loop darts (K, K). This keeps every base vertex at degree d, adds 2G
vertices, and leaves the old blocks with their degrees intact. Annealing then
repairs the diameter using voltage changes and endpoint-swap moves on
darts. The chain K = 2, 3, ... continues while annealing succeeds, and
every valid stage is checked with lib.is_valid.
"""
import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KMAX = 8  # 2K bits must fit in the popcount table


# ----------------------------------------------------------------------------
# Exact families for the small calibration cases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_for(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 (D = 3 only)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Groups: Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e).
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
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


# ----------------------------------------------------------------------------
# Base multigraph = list of darts (i, j, s): A_i and B_j joined by voltage s.
# Every base vertex carries exactly d darts, so the lift is d-regular.
# ----------------------------------------------------------------------------

def _random_regular(K, G, d, rng):
    darts = []
    for _ in range(d):
        perm = rng.sample(range(K), K)
        for i in range(K):
            darts.append((i, perm[i], rng.randrange(G)))
    return darts


def _grow(darts, K, G, d, rng):
    """Orbit insertion: K blocks per side become K+1. Degrees stay d."""
    y = rng.randrange(1, d)          # number of A_K-B_K darts
    t = d - y                        # darts removed from the old base
    idx = set(rng.sample(range(len(darts)), t))
    new = [darts[e] for e in range(len(darts)) if e not in idx]
    for e in idx:
        i, j, _ = darts[e]
        new.append((i, K, rng.randrange(G)))
        new.append((K, j, rng.randrange(G)))
    for _ in range(y):
        new.append((K, K, rng.randrange(G)))
    return new


def _build_nbr(K, G, d, darts, Ts, Invs):
    """Neighbour table (d rows): row la gives A-side slot la, row lb gives B-side slot lb."""
    nbr = np.zeros((d, 2 * K * G), dtype=np.int64)
    sa = [0] * K
    sb = [0] * K
    for i, j, s in darts:
        la = sa[i]
        sa[i] += 1
        lb = sb[j]
        sb[j] += 1
        nbr[la, i * G:(i + 1) * G] = (K + j) * G + Ts[s]
        nbr[lb, (K + j) * G:(K + j + 1) * G] = i * G + Invs[s]
    return nbr


def _reach(K, G, D, nbr, d):
    """Bit b of reach[v] is set when representative block b is within distance D of v."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * K):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(K, N, reach):
    return 2 * K * N - int(_POP[reach].sum())


def _anneal(K, G, d, D, darts, rng, deadline, Ts, Invs, iters, patience):
    """Simulated annealing on darts. Returns (darts, cost); cost 0 means diameter <= D."""
    N = 2 * K * G
    full = (1 << (2 * K)) - 1

    def evaluate(ds):
        nbr = _build_nbr(K, G, d, ds, Ts, Invs)
        reach = _reach(K, G, D, nbr, d)
        dup = len(ds) - len(set(ds))
        return _unreached(K, N, reach) + _PENALTY * dup, reach

    cost, reach = evaluate(darts)
    c0 = float(max(cost, 1))
    best, last = cost, 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline or t - last > patience:
            break
        temp = max(0.5, 0.02 * c0 * (1.0 - t / iters))
        new = list(darts)
        if rng.random() < 0.3 and len(new) >= 2:
            # Endpoint swap: keeps every base degree unchanged.
            e1, e2 = rng.sample(range(len(new)), 2)
            i1, j1, s1 = new[e1]
            i2, j2, s2 = new[e2]
            if j1 == j2:
                continue
            new[e1] = (i1, j2, s1)
            new[e2] = (i2, j1, s2)
        else:
            bad = np.flatnonzero(reach != full)
            if bad.size and rng.random() < 0.5:
                # Defect-targeted voltage move: a dart touching a bad block.
                u = int(bad[rng.randrange(bad.size)])
                blk = u // G
                if blk < K:
                    cands = [e for e, (i, j, s) in enumerate(new) if i == blk]
                else:
                    cands = [e for e, (i, j, s) in enumerate(new) if j == blk - K]
                e = rng.choice(cands) if cands else rng.randrange(len(new))
            else:
                e = rng.randrange(len(new))
            i, j, s = new[e]
            ns = rng.randrange(G)
            if ns == s:
                continue
            new[e] = (i, j, ns)
        c2, r2 = evaluate(new)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            darts, cost, reach = new, c2, r2
            if cost < best:
                best, last = cost, t
    return darts, cost


def _edges(K, G, darts, Ts):
    """Materialise the lift: edge (i*G+g, (K+j)*G + g*s) for every dart."""
    edges = []
    base = np.arange(G, dtype=np.int64)
    for i, j, s in darts:
        a = i * G + base
        b = (K + j) * G + Ts[s]
        edges.extend(zip(a.tolist(), b.tolist()))
    return 2 * K * G, edges


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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact calibration constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3:
            ar = _araujo_for(d)
            if ar is not None:
                consider(ar[0], ar[1])

    if d < 2:
        return best

    # Chain search: fix a group, grow the base by orbit insertion while annealing succeeds.
    while time.monotonic() < deadline:
        Kt = rng.choice((3, 4, 5, 6))
        target = max(2, best_n // (2 * Kt) + 1 + rng.randrange(0, 6))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        K = 2
        darts = _random_regular(K, G, d, rng)
        while time.monotonic() < deadline:
            darts, cost = _anneal(K, G, d, D, darts, rng, deadline, Ts, Invs, 3000, 900)
            if cost != 0:
                break
            if 2 * K * G > best_n:
                n_, e_ = _edges(K, G, darts, Ts)
                consider(n_, e_)
            if K >= _KMAX:
                break
            darts = _grow(darts, K, G, d, rng)
            K += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
