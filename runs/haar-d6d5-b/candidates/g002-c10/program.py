"""Voltage lifts of a 2+2 bipartite base multigraph over non-cyclic groups (numpy only), with a Haar fallback.

NEW FAMILY (replaces the Haar annealing for d=6, D=5).  The base graph has two A-vertices and two B-vertices.
A-vertex i and B-vertex j are joined by M[i][j] darts, with M = [[p, d-p], [d-p, p]], so every base vertex has
degree d.  Each dart carries a group element g, and the lift of a dart from A_i to B_j joins (A_i, x) to
(B_j, x*g).  Left multiplication by any h in G is an automorphism that acts regularly on each class of 2|G|/2
copies, so diameter <= D holds iff the balls of radius D around the four identity copies (A0,e), (A1,e), (B0,e),
(B1,e) cover the whole graph.  This gives an exact cost (number of uncovered vertices, summed over those four
BFS sources) that needs only four BFS passes per evaluation.

The search anneals the voltages inside each (group, p) attempt, with restarts when stuck.  The lift has 4|G|
vertices, so the target is |G| >= 172 (4*172 = 688 > 684).  Every returned graph is checked with lib.is_valid.
If nothing is found in time, the valid Haar fallback (660 vertices) is returned.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

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
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    return 2 * N, [(g, N + int(MT[s, g])) for s in S for g in range(N)]


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ voltage-lift search

def attempt(MT, inv, N, d, D, p, rng, t_end):
    """Anneal the voltages of the 2+2 base lift over the group with table MT until the lift has diameter <= D.
    Returns (n, edges) for a checked graph, or None."""
    M = [[p, d - p], [d - p, p]]
    di_l, dj_l = [], []
    for i in range(2):
        for j in range(2):
            for _ in range(M[i][j]):
                di_l.append(i)
                dj_l.append(j)
    di = np.array(di_l, dtype=np.int64)
    dj = np.array(dj_l, dtype=np.int64)
    T = len(di)
    idxA = [np.nonzero(di == i)[0] for i in range(2)]
    idxB = [np.nonzero(dj == j)[0] for j in range(2)]
    ar = np.arange(N)
    n = 4 * N

    def build_adj(G):
        adj = np.empty((n, d), dtype=np.int64)
        for i in range(2):
            ids = idxA[i]
            adj[i * N:(i + 1) * N] = 2 * N + dj[ids][None, :] * N + MT[:, G[ids]]
        for j in range(2):
            ids = idxB[j]
            adj[2 * N + j * N:2 * N + (j + 1) * N] = (
                di[ids][None, :] * N + MT[ar[:, None], inv[G[ids]][None, :]])
        return adj

    def cost(G):
        adj = build_adj(G)
        tot = 0
        for s in (0, N, 2 * N, 3 * N):
            seen = np.zeros(n, dtype=bool)
            seen[s] = True
            fr = np.array([s], dtype=np.int64)
            for _ in range(D):
                nb = adj[fr].ravel()
                nb = nb[~seen[nb]]
                if nb.size == 0:
                    break
                nb = np.unique(nb)
                seen[nb] = True
                fr = nb
            tot += n - int(seen.sum())
        return tot

    def random_G():
        G = np.empty(T, dtype=np.int64)
        for i in range(2):
            for j in range(2):
                sel = np.nonzero((di == i) & (dj == j))[0]
                if len(sel):
                    G[sel] = rng.choice(N, len(sel), replace=False)
        return G

    G = random_G()
    cur = cost(G)
    best, since = cur, 0
    while time.monotonic() < t_end and cur > 0:
        t = int(rng.integers(T))
        sel = np.nonzero((di == di[t]) & (dj == dj[t]))[0]
        used = set(G[sel].tolist())
        g = int(rng.integers(N))
        if g in used:
            continue
        old = G[t]
        G[t] = g
        new = cost(G)
        if new <= cur or rng.random() < math.exp(-(new - cur) / 0.6):
            cur = new
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            G[t] = old
            since += 1
        if since > 3000:
            G = random_G()
            cur = cost(G)
            best, since = cur, 0

    if cur == 0:
        adj = build_adj(G)
        edges = [(u, int(v)) for u in range(2 * N) for v in adj[u]]
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


def candidate_groups(rng, lo=172, hi=200):
    """(m, k, lam) for Z_m x|_lam Z_k with lo <= m*k <= hi; non-abelian (lam != 1) listed first."""
    nonab, ab = [], []
    for N in range(lo, hi + 1):
        for k in range(1, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            for lam in range(1, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                (ab if lam == 1 else nonab).append((m, k, lam))
    rng.shuffle(nonab)
    rng.shuffle(ab)
    return nonab + ab


# ----------------------------------------------------------------------------------------- the build

TARGET = (6, 5)

# Valid smaller Haar graph (660 vertices), used only if the lift search finds nothing.
FALLBACK_GROUP = (33, 10, 26)
FALLBACK_S = [0, 179, 116, 180, 47, 306]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    try:
        groups = candidate_groups(rng)
        for (m, k, lam) in groups:
            if time.monotonic() >= end_all:
                break
            try:
                MT, inv = group_meta(m, k, lam)
            except Exception:
                continue
            N = m * k
            for p in (3, 2, 1):
                now = time.monotonic()
                if now >= end_all:
                    break
                slice_end = now + min(end_all - now, 4.0)
                try:
                    res = attempt(MT, inv, N, d, D, p, rng, slice_end)
                except Exception:
                    res = None
                if res is not None:
                    return res
    except Exception:
        pass
    try:
        MT, _ = group_meta(*FALLBACK_GROUP)
        n, edges = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
