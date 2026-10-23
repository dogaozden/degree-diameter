"""Bipartite degree-diameter search for (d=10, D=5): voltage lifts of a 2-fibre base over metacyclic groups.

Construction: a base graph with two A-fibres and two B-fibres. A-fibre i and B-fibre j are joined by
block (i, j) of m_ij voltages s, giving edges (g, A_i) ~ (s*g, B_j). Here m = [[k, d-k], [d-k, k]], so
every vertex has degree d. The lift has 4|G| vertices, so |G| >= 1001 beats the record of 4000.
Right multiplication is an automorphism, so the diameter is exact if BFS runs from the four
fibre identities. The cost is the number of vertices left unreached within D. Simulated annealing
on the voltages runs over several metacyclic groups. A solution is returned only after lib.is_valid.
If nothing is found, the previous checked Haar graph (3582 vertices) is returned, and other
cases get small checked graphs.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
TEMP = 2.0
PATIENCE = 3000


# ----------------------------------------------------------------------- groups

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a,j)(b,l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 128):
        hi = min(N, lo + 128)
        MT[lo:hi] = (((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k
                     + (j[lo:hi, None] + j[None, :]) % k)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def _candidates(lo, hi):
    """Non-abelian metacyclic groups Z_m x| Z_k with order N = m*k in [lo, hi]."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            found = 0
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((N, m, k, lam))
                    found += 1
                    if found == 2:
                        break
    return out


# ----------------------------------------------------------------------- lift

TOPT = 0  # unused placeholder to keep structure simple


def _lift_nbr(MT, inv, V, N, d):
    """Neighbour array (4N, d). A-fibre i is index i*N+g, B-fibre j is index 2N+j*N+h."""
    n = 4 * N
    nbr = np.empty((n, d), dtype=np.int64)
    for i in range(2):
        parts = [(2 * N + j * N) + MT[V[i][j]].T.astype(np.int64) for j in range(2)]
        nbr[i * N:(i + 1) * N] = np.concatenate(parts, axis=1)
    for j in range(2):
        parts = [i * N + MT[inv[V[i][j]]].T.astype(np.int64) for i in range(2)]
        nbr[2 * N + j * N:2 * N + (j + 1) * N] = np.concatenate(parts, axis=1)
    return nbr


def _lift_cost(nbr, N, D):
    """Total vertices unreached within D from the four fibre identities (0 means diameter <= D)."""
    n = nbr.shape[0]
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            cand = nbr[frontier].ravel()
            cand = cand[~seen[cand]]
            if cand.size == 0:
                break
            cand = np.unique(cand)
            seen[cand] = True
            frontier = cand
        total += n - int(seen.sum())
    return total


def _lift_edges(nbr, N):
    n = 4 * N
    A = np.repeat(np.arange(2 * N, dtype=np.int64), nbr.shape[1])
    B = nbr[:2 * N].ravel()
    return n, list(zip(A.tolist(), B.tolist()))


def _anneal(MT, inv, N, d, D, rng, deadline):
    """Anneal voltages for one random block size. Returns (V, nbr) with cost 0, or None."""
    kk = int(rng.integers(3, 8))
    M = [[kk, d - kk], [d - kk, kk]]
    V = [[rng.choice(N, size=M[i][j], replace=False).astype(np.int64) for j in range(2)] for i in range(2)]
    nbr = _lift_nbr(MT, inv, V, N, d)
    cur = _lift_cost(nbr, N, D)
    best, stall = cur, 0
    while True:
        if cur == 0:
            return V, nbr
        if stall > PATIENCE or time.monotonic() >= deadline:
            return None
        i = int(rng.integers(2))
        j = int(rng.integers(2))
        S = V[i][j]
        x = int(rng.integers(N))
        if np.any(S == x):
            stall += 1
            continue
        t = int(rng.integers(len(S)))
        newS = S.copy()
        newS[t] = x
        Vn = [list(V[0]), list(V[1])]
        Vn[i][j] = newS
        nb = _lift_nbr(MT, inv, Vn, N, d)
        c = _lift_cost(nb, N, D)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            V, nbr, cur = Vn, nb, c
        if cur < best:
            best, stall = cur, 0
        else:
            stall += 1


def _lift_search(d, D, seed, deadline):
    """Try several groups of order in [1001, 1040]; return a checked (n, edges) or None."""
    rng = np.random.default_rng(seed)
    cands = _candidates(1001, 1040)
    if not cands:
        return None
    order = rng.permutation(len(cands))
    idx = 0
    while time.monotonic() < deadline - 2.0:
        N, m, k, lam = cands[int(order[idx % len(order)])]
        idx += 1
        slice_end = min(deadline, time.monotonic() + 6.0)
        MT, inv = group_meta(m, k, lam)
        while time.monotonic() < slice_end:
            res = _anneal(MT, inv, N, d, D, rng, slice_end)
            if res is None:
                continue
            V, nbr = res
            n, edges = _lift_edges(nbr, N)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


# ----------------------------------------------------------------------- fallbacks

def _haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def _checked_fallback(d, D):
    """Previously verified Haar graph on 3582 vertices (group Z_199 x| Z_9)."""
    MT, _ = group_meta(199, 9, 180)
    S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
    n, edges = _haar_edges(MT, S)
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def _trivial(d, D):
    options = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        options.append(lib.projective_plane_incidence(d - 1))
    options.append((2, [(0, 1)]))
    options.append((1, []))
    for n, edges in options:
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return 1, []


# ----------------------------------------------------------------------- entry

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _trivial(d, D)
    t0 = time.monotonic()
    search_end = t0 + 0.70 * time_limit
    try:
        res = _lift_search(d, D, seed, search_end)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        res = _checked_fallback(d, D)
        if res is not None:
            return res
    except Exception:
        pass
    return _trivial(d, D)
