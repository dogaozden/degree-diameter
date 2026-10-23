"""Bi-Cayley (two-orbit-per-side) search for the d=6, D=5 target, with a valid Haar fallback.

THEORY.  Let G be a finite group of order N.  Use two A-orbits (i = 0, 1) and two B-orbits (j = 0, 1),
so there are 4N vertices.  For each (i, j) pick a set S[i][j] of P[i][j] group elements, with
P[i][0] + P[i][1] = d for each i and P[0][j] + P[1][j] = d for each j.  Edges are
(i, g) ~ (j, s*g) for s in S[i][j].  Right multiplication by any h in G is an automorphism that
acts regularly on each orbit, so the diameter can be checked by BFS from only the four vertices
(e, orbit).  That makes the cost evaluation cheap.  Cost = number of (source, vertex) pairs not
reached within distance D.  Cost 0 means the graph is valid.

With 4N vertices and d = 6, N >= 172 gives a graph larger than the record 684.

PLAN.  Search many non-abelian groups of order 172..196 (metacyclic Z_m x| Z_k, plus Heis(3) x Z_7)
with simulated annealing (best-of-K moves, Metropolis acceptance, restarts).  Every candidate is
checked with lib.is_valid before it is returned.  If nothing is found in time, the valid Haar
graph on 660 vertices is returned, and K_{6,6} is the last resort.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
FALLBACK_S = [0, 179, 116, 180, 47, 306]   # valid Haar graph on 660 vertices in Z_33 x| Z_10
K_CANDIDATES = 6
TEMP = 1.0
PATIENCE = 600
SLICE_SECONDS = 6.0


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    if pow(lam, k, m) != 1 % m:
        raise ValueError("bad metacyclic parameters")
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
    """Table of a group given as an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        block = MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k
        MT[g * k:(g + 1) * k] = block.reshape(k, n0 * k)
    return _finish(MT)


def candidate_specs():
    """Non-abelian metacyclic groups of order 172..196 (one lam per (m, k)), then Heis(3) x Z_7 (order 189)."""
    specs = []
    for N in range(172, 197):
        for k in range(2, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    specs.append(('meta', m, k, lam))
                    break
    specs.append(('heis', 3, 7))
    return specs


# ------------------------------------------------------------------------- two-orbit bi-Cayley search

def build_nbr(MT, inv, S, N):
    """Neighbour array (4N x d) of the bi-Cayley graph.  Orbit o occupies rows o*N..o*N+N-1.
    Orbits 0,1 are A-orbits and 2,3 are B-orbits.  Right multiplication is an automorphism."""
    g = np.arange(N, dtype=np.int64)
    rows = []
    for i in range(2):
        cols = []
        for j in range(2):
            for s in S.get((i, j), []):
                cols.append((2 + j) * N + MT[int(s), g].astype(np.int64))
        rows.append(np.stack(cols, axis=1))
    for j in range(2):
        cols = []
        for i in range(2):
            for s in S.get((i, j), []):
                cols.append(i * N + MT[int(inv[int(s)]), g].astype(np.int64))
        rows.append(np.stack(cols, axis=1))
    return np.vstack(rows)


def cost_pattern(nbr, N, D=5):
    """Unreached (source, vertex) pairs within distance D, summed over the four orbit representatives."""
    M = nbr.shape[0]
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        reach = np.zeros(M, dtype=bool)
        reach[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = np.zeros(M, dtype=bool)
            nxt[nbr[front].ravel()] = True
            nxt &= ~reach
            if not nxt.any():
                break
            reach |= nxt
            front = np.flatnonzero(nxt)
        total += M - int(np.count_nonzero(reach))
    return total


def graph_from(MT, inv, S, N):
    nbr = build_nbr(MT, inv, S, N)
    edges = [(u, int(v)) for u in range(2 * N) for v in nbr[u]]
    return 4 * N, edges


def anneal(MT, inv, P, N, deadline, rng, D=5):
    """Simulated annealing over the 2x2 connection sets.  Returns a zero-cost S dict, or None."""
    cells = [(i, j) for i in range(2) for j in range(2) if P[i][j] > 0]

    def cost_of(S):
        return cost_pattern(build_nbr(MT, inv, S, N), N, D)

    while time.monotonic() < deadline:
        S = {c: rng.choice(N, P[c[0]][c[1]], replace=False).astype(np.int64) for c in cells}
        cur = cost_of(S)
        if cur == 0:
            return S
        stall, bestrun = 0, cur
        while time.monotonic() < deadline and stall < PATIENCE:
            c = cells[int(rng.integers(len(cells)))]
            arr = S[c]
            pos = int(rng.integers(len(arr)))
            bestnew, bestcc = None, 10 ** 9
            for _ in range(K_CANDIDATES):
                x = int(rng.integers(N))
                if x in arr:
                    continue
                new = arr.copy()
                new[pos] = x
                S2 = dict(S)
                S2[c] = new
                cc = cost_of(S2)
                if cc < bestcc:
                    bestcc, bestnew = cc, new
            if bestnew is None:
                continue
            delta = bestcc - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                S[c] = bestnew
                cur = bestcc
                if cur == 0:
                    return S
                if cur < bestrun:
                    bestrun, stall = cur, 0
                else:
                    stall += 1
            else:
                stall += 1
    return None


def search_orbits(d, D, seed, end):
    """Round-robin annealing over (group, pattern) combinations.  Returns a checked (n, edges) or None."""
    rng = np.random.default_rng(seed)
    patterns = [((3, 3), (3, 3)), ((4, 2), (2, 4))]
    groups = []
    for spec in candidate_specs():
        try:
            if spec[0] == 'meta':
                MT, inv = group_meta(spec[1], spec[2], spec[3])
            else:
                MT, inv = group_times_cyclic(group_heis(spec[1]), spec[2])
        except Exception:
            continue
        if MT.shape[0] * 4 >= 685:
            groups.append((MT, inv))
        if len(groups) >= 4:
            break
    combos = [(g, p) for g in groups for p in patterns]
    if not combos:
        return None
    cyc = 0
    while time.monotonic() < end - 1.0:
        (MT, inv), P = combos[cyc % len(combos)]
        N = MT.shape[0]
        slice_end = min(end, time.monotonic() + SLICE_SECONDS)
        try:
            S = anneal(MT, inv, P, N, slice_end, rng)
        except Exception:
            S = None
        if S is not None:
            n, edges = graph_from(MT, inv, S, N)
            if lib.is_valid(n, edges, d, D):
                return n, edges
        cyc += 1
    return None


# ------------------------------------------------------------------------------- fallbacks

def haar_graph_from(MT, S):
    """Haar graph of group table MT and set S: A-vertex g is g, B-vertex g is N+g, (g,A) ~ (s*g,B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end = t0 + max(1.0, min(0.80 * time_limit, time_limit - 8.0))
    try:
        res = search_orbits(d, D, seed, end)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        MT, _ = group_meta(33, 10, 26)
        n, edges = haar_graph_from(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
