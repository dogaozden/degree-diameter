"""d=10, D=5 search: non-abelian voltage lifts of a 2+2 bipartite base (numpy + lib).

Construction: base graph with A0, A1 (left) and B0, B1 (right), each base vertex of degree d.
The multiplicity matrix is [[c, d-c], [d-c, c]]. Each dart (a, b, g) with voltage g in a group G
joins (a, x) to (b, x*g). The lift is bipartite, d-regular, and has 4|G| vertices.

Left multiplication by any h in G is an automorphism, so the diameter is at most D iff a BFS of depth D
from each of the four base vertices (v, identity) reaches every vertex. The cost is the total number of
unreached vertices over those four BFS runs; cost 0 means valid. Annealing moves change one dart voltage.

Safe fallback: a fixed valid Haar graph on 3582 vertices, checked with lib.is_valid, and the trivial
graph for any other (d, D).
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _candidates(lo, hi):
    """Non-trivial metacyclic groups Z_m x| Z_k with order in [lo, hi], largest order first."""
    out = []
    for k in range(2, 12):
        for m in range(max(3, lo // k), hi // k + 1):
            if m * k < lo or m * k > hi:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((m * k, m, k, lam))
                    break
    out.sort(reverse=True)
    return out


# ----------------------------------------------------------------------------- lift model

def _neighbours(MT, inv, N, d, g, pa, pb, idxA, idxB):
    """Neighbour table (4N x d) of the lift. Vertex ids: base vertex v in {0,1,2,3} -> v*N + x.
    Base 0,1 are A-side; base 2,3 are B-side. The dart (a, b, g) joins (a, x) to (b, x*g)."""
    nb = np.empty((4 * N, d), dtype=np.int64)
    for a in (0, 1):
        ts = idxA[a]
        nb[a * N:(a + 1) * N] = (2 + pb[ts])[None, :] * N + MT[:, g[ts]]
    for b in (0, 1):
        ts = idxB[b]
        nb[(2 + b) * N:(3 + b) * N] = pa[ts][None, :] * N + MT[:, inv[g[ts]]]
    return nb


def _unreached(nb, src, D, total):
    """Number of vertices NOT within distance D of src."""
    seen = np.zeros(total, dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(D):
        nxt = nb[frontier].ravel()
        nxt = np.unique(nxt[~seen[nxt]])
        if nxt.size == 0:
            break
        seen[nxt] = True
        frontier = nxt
    return total - int(seen.sum())


def _cost(MT, inv, N, d, D, g, pa, pb, idxA, idxB):
    """Total unreached count over the four base-vertex sources. Zero iff the lift has diameter <= D."""
    nb = _neighbours(MT, inv, N, d, g, pa, pb, idxA, idxB)
    total = 4 * N
    return sum(_unreached(nb, v * N, D, total) for v in range(4))


def _structure(d, c0):
    """Dart structure for multiplicity matrix [[c0, d-c0], [d-c0, c0]]."""
    pa = np.array([0] * d + [1] * d, dtype=np.int64)
    pb = np.array([0] * c0 + [1] * (d - c0) + [0] * (d - c0) + [1] * c0, dtype=np.int64)
    idxA = [np.nonzero(pa == a)[0] for a in (0, 1)]
    idxB = [np.nonzero(pb == b)[0] for b in (0, 1)]
    return pa, pb, idxA, idxB


def _anneal(MT, inv, N, d, D, deadline, rng, stall=2500, T=0.8):
    """Simulated annealing on the dart voltages. Returns (g, pa, pb) with cost 0, or None at the deadline."""
    while time.monotonic() < deadline:
        c0 = int(rng.integers(1, d))
        pa, pb, idxA, idxB = _structure(d, c0)
        pair = 2 * pa + pb
        g = np.zeros(2 * d, dtype=np.int64)
        for p in range(4):
            idx = np.nonzero(pair == p)[0]
            g[idx] = rng.choice(N, size=len(idx), replace=False)  # distinct voltages on parallel darts
        cur = _cost(MT, inv, N, d, D, g, pa, pb, idxA, idxB)
        best_here, since = cur, 0
        while cur > 0 and since < stall and time.monotonic() < deadline:
            t = int(rng.integers(2 * d))
            p = pair[t]
            others = g[(pair == p) & (np.arange(2 * d) != t)]
            x = int(rng.integers(N))
            while x in others:
                x = int(rng.integers(N))
            old = g[t]
            g[t] = x
            new = _cost(MT, inv, N, d, D, g, pa, pb, idxA, idxB)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
                if cur < best_here:
                    best_here, since = cur, 0
                else:
                    since += 1
            else:
                g[t] = old
                since += 1
        if cur == 0:
            return g, pa, pb
    return None


def _lift_edges(MT, inv, N, d, g, pa, pb, idxA, idxB):
    nb = _neighbours(MT, inv, N, d, g, pa, pb, idxA, idxB)
    edges = []
    for u in range(2 * N):  # A-side rows only: every edge appears once
        for w in nb[u].tolist():
            edges.append((u, w))
    return 4 * N, edges


# ----------------------------------------------------------------------------- fallback and trivial

def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def _fallback(d, D):
    """Valid smaller Haar graph (order 3582 at d=10, D=5), checked at run time."""
    try:
        MT, _ = group_meta(199, 9, 180)
        S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
        n, edges = haar_edges(MT, S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return _trivial(d, D)


def _trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
    rng = np.random.default_rng(seed)
    cands = _candidates(896, 1100)[:20]
    for idx, (order, m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        slot = (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            N = m * k
            res = _anneal(MT, inv, N, d, D, now + slot, rng)
            if res is not None:
                g, pa, pb = res
                pa, pb, idxA, idxB = _structure(d, int(np.count_nonzero(pa[:d] == pb[:d])))
                # Rebuild the structure exactly as searched (c0 is recovered from the pair pattern).
                n, edges = _lift_edges(MT, inv, N, d, g, pa, pb, idxA, idxB)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
        except Exception:
            continue
    return _fallback(d, D)
