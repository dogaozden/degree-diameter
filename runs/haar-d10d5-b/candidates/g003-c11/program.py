"""Two-orbit voltage lifts for the bipartite degree-diameter problem at (d=10, D=5), with a safe fallback.

CONSTRUCTION.  Take a finite group G of order N and a base bipartite multigraph on a+a vertices
(A_0..A_{a-1}, B_0..B_{a-1}) whose every vertex has degree d.  Each base dart (A_i, B_j, g) gives the lift
edges (A_i, x) ~ (B_j, x*g) for all x in G.  Left multiplication by h in G is an automorphism, so the
diameter of the lift equals the maximum eccentricity of the 2a base vertices at the identity.  This gives a
cheap exact cost: propagate a bitmask of "which base sources reach me" for 5 rounds over the lift, and count
the (source, vertex) pairs still unreached.  Cost 0 means diameter <= 5.

Here a = 2, so the lift has 4N vertices and degree d.  The base matrix is [[k, d-k], [d-k, k]].  Voltages
within each base pair are kept distinct, so the lift is simple.  Groups have order N about 1000, giving
4N > 4000 vertices when the search succeeds.

SAFETY.  A validated Haar graph of 3582 vertices is computed first and kept.  Any lift is returned only after
lib.is_valid accepts it.  If nothing better is found, the fallback is returned.
"""
import itertools
import math
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------- lift construction

def _pairs(a, M):
    """Flat list of base darts (i, j): M[i][j] copies of each pair."""
    return [(i, j) for i in range(a) for j in range(a) for _ in range(M[i][j])]


def build_nbr(MT, inv, a, d, pairs, volts):
    """Neighbour array (V, d) of the lift.  A-block i is index i*N + x; B-block j is index (a+j)*N + y."""
    N = MT.shape[0]
    x = np.arange(N, dtype=np.int64)
    nbr = np.empty((2 * a * N, d), dtype=np.int64)
    cA = [0] * a
    cB = [0] * a
    for (i, j), g in zip(pairs, volts):
        nbr[i * N:(i + 1) * N, cA[i]] = (a + j) * N + MT[x, g]
        cA[i] += 1
        nbr[(a + j) * N:(a + j + 1) * N, cB[j]] = i * N + MT[x, inv[g]]
        cB[j] += 1
    return nbr


POP = np.array([bin(v).count("1") for v in range(256)], dtype=np.int64)


def _cost(nbr, a, N):
    """Number of (base source, lift vertex) pairs at distance > 5 from the source at the identity."""
    V = nbr.shape[0]
    reach = np.zeros(V, dtype=np.uint8)
    for s in range(2 * a):
        reach[s * N] = np.uint8(int(reach[s * N]) | (1 << s))
    for _ in range(5):
        new = reach.copy()
        for c in range(nbr.shape[1]):
            new |= reach[nbr[:, c]]
        reach = new
    full = (1 << (2 * a)) - 1
    missing = (~reach) & np.uint8(full)
    return int(POP[missing].sum())


def anneal(MT, inv, a, d, M, deadline, rng, stall=2500, temp=1.5):
    """Simulated annealing over voltages with the base matrix M fixed.  Returns (best cost, best voltages)."""
    N = MT.shape[0]
    pairs = _pairs(a, M)
    T = len(pairs)
    same = [[u for u in range(T) if u != t and pairs[u] == pairs[t]] for t in range(T)]
    volts = [-1] * T

    def pick(t):
        used = {volts[u] for u in same[t]}
        while True:
            g = int(rng.integers(N))
            if g not in used:
                return g

    for t in range(T):
        volts[t] = pick(t)
    cur = _cost(build_nbr(MT, inv, a, d, pairs, volts), a, N)
    best_c, best_v = cur, list(volts)
    stale = 0
    while cur > 0 and stale < stall and time.monotonic() < deadline:
        t = int(rng.integers(T))
        old = volts[t]
        volts[t] = pick(t)
        c = _cost(build_nbr(MT, inv, a, d, pairs, volts), a, N)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = c
            if cur < best_c:
                best_c, best_v, stale = cur, list(volts), 0
            else:
                stale += 1
        else:
            volts[t] = old
            stale += 1
    return best_c, best_v


def _graph_from(MT, inv, a, d, M, volts):
    """Edge list of the lift if its cost is 0, else None."""
    N = MT.shape[0]
    pairs = _pairs(a, M)
    nbr = build_nbr(MT, inv, a, d, pairs, volts)
    if _cost(nbr, a, N) != 0:
        return None
    n = 2 * a * N
    src = np.repeat(np.arange(a * N, dtype=np.int64), d)
    dst = nbr[:a * N].ravel()
    return n, list(zip(src.tolist(), dst.tolist()))


# ------------------------------------------------------------------------------------- candidates

def _meta_candidates(lo, hi, limit):
    """Metacyclic groups Z_m x| Z_k with lo <= m*k <= hi and lam != trivial, as (order, m, k, lam)."""
    out = []
    for m in range(3, hi):
        for k in range(2, hi // m + 1):
            n = m * k
            if n < lo or n > hi:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((n, m, k, lam))
                    break
            if len(out) >= limit:
                return out
    return out


def candidates():
    C = [
        (1008, lambda: group_times_cyclic(group_sl2(7), 3)),
        (1029, lambda: group_times_cyclic(group_heis(7), 3)),
    ]
    for n, m, k, lam in _meta_candidates(1001, 1060, 3):
        C.append((n, lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    C.append((1000, lambda: group_times_cyclic(group_heis(5), 8)))
    return C


# ------------------------------------------------------------------------------- safe fallbacks

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    if d <= 0:
        return 1, []
    if D >= 2:
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]   # K_{d,d}, diameter 2
    return 2, [(0, 1)]


def fallback_graph(d, D):
    """Validated Haar graph of order 3582 for (10, 5); otherwise trivial."""
    try:
        MT, _ = group_meta(199, 9, 180)
        S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
        n, edges = haar_edges(MT, S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------------------------ build

TARGET = (10, 5)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + max(2.0, 0.72 * time_limit - 3.0)
    best = fallback_graph(d, D)
    rng = np.random.default_rng(seed)
    cands = candidates()
    for idx, (order, builder) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        slot_end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = builder()
        except Exception:
            continue
        N = MT.shape[0]
        while time.monotonic() < slot_end - 0.5:
            k = int(rng.choice([3, 4, 5, 6, 7]))
            M = [[k, d - k], [d - k, k]]
            end = min(slot_end, time.monotonic() + 4.0)
            try:
                c, volts = anneal(MT, inv, 2, d, M, end, rng)
            except Exception:
                break
            if c == 0:
                try:
                    g = _graph_from(MT, inv, 2, d, M, volts)
                except Exception:
                    g = None
                if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                    return g
    return best
