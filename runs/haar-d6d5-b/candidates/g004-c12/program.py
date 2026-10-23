"""Haar-graph search over non-abelian metacyclic groups for the (d=6, D=5) target.

CONSTRUCTION.  Take a group G of order M and a set S of 6 distinct elements.  The Haar graph has
A-vertices g and B-vertices M+g, with edges g ~ M + s*g for s in S.  It is bipartite and 6-regular
on 2M vertices.  Right multiplication by h is an automorphism (g -> g*h on both sides), so the A-side
and B-side are each vertex-transitive.  Diameter <= 5 therefore holds iff the radius-5 balls around
the two identities (A-vertex 0 and B-vertex M) cover all 2M vertices.

COST.  cost(S) = uncovered vertices in those two balls.  cost 0 means the graph is valid, and every
result is still checked with lib.is_valid before it is returned.

SEARCH.  Simulated annealing over S with random restarts, on several non-abelian metacyclic groups
Z_m x|_lam Z_k with orders in 336..400.  The time budget is split evenly across the candidate groups,
and any unused time rolls forward.  The best valid graph wins.  If nothing beats the verified
660-vertex Haar fallback, that fallback is returned.
"""
import math
import time
from math import gcd

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
RADIUS = 5


# ----------------------------------------------------------------------------- groups

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m.

    Returns (MT, inv): multiplication table and inverse array; identity is index 0.
    """
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def candidates(rng, lo=336, hi=400, cap=10):
    """One non-abelian metacyclic group per order in [lo, hi] (chosen at random), evenly spread, capped."""
    found = []
    for M in range(lo, hi + 1):
        triples = []
        for m in range(2, M // 2 + 1):
            if M % m:
                continue
            k = M // m
            if k < 2:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    triples.append((m, k, lam))
                    break
        if triples:
            found.append(triples[int(rng.integers(len(triples)))])
    if len(found) > cap:
        idx = np.linspace(0, len(found) - 1, cap).round().astype(int)
        found = [found[i] for i in idx]
    return found


# ----------------------------------------------------------------------------- search

def search(MT, inv, M, end, rng, T=1.5, patience=2500):
    """Anneal a 6-element set S so that the Haar graph of G with S has diameter <= 5.  Returns S or None."""
    N = 2 * M

    def build_nbr(S):
        Sa = np.array(S, dtype=np.int64)
        nbr = np.empty((N, DEG), dtype=np.int64)
        nbr[:M] = M + MT[Sa].T          # A-vertex g -> B-vertex M + s*g
        nbr[M:] = MT[inv[Sa]].T         # B-vertex M + y -> A-vertex s^-1 * y
        return nbr

    def cover(nbr, src):
        vis = np.zeros(N, dtype=bool)
        vis[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(RADIUS):
            nb = nbr[front].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            new = np.zeros(N, dtype=bool)
            new[nb] = True
            vis |= new
            front = np.flatnonzero(new)
        return N - int(vis.sum())

    def cost(S):
        nbr = build_nbr(S)
        return cover(nbr, 0) + cover(nbr, M)

    while time.monotonic() < end:
        S = [int(x) for x in rng.choice(M, DEG, replace=False)]
        cur = cost(S)
        since = 0
        while since < patience and time.monotonic() < end:
            if cur == 0:
                return S
            k = int(rng.integers(DEG))
            x = int(rng.integers(M))
            if x in S:
                continue
            S2 = S.copy()
            S2[k] = x
            c2 = cost(S2)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = S2, c2
                since = 0 if delta < 0 else since + 1
            else:
                since += 1
        if cur == 0:
            return S
    return None


def to_edges(MT, M, S):
    edges = []
    for s in S:
        for g in range(M):
            edges.append((g, M + int(MT[s, g])))
    return 2 * M, edges


# ----------------------------------------------------------------------------- fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Valid 660-vertex Haar graph (group_meta(33, 10, 26))."""
    MT, _ = group_meta(33, 10, 26)
    N = MT.shape[0]
    edges = []
    for s in FALLBACK_S:
        for g in range(N):
            edges.append((g, N + int(MT[s, g])))
    return 2 * N, edges


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return 2, [(0, 1)]


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None  # (n, edges)
    try:
        n, e = haar_fallback()
        if lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass

    cands = candidates(rng)
    for idx, (m, k, lam) in enumerate(cands):
        M = m * k
        if best is not None and 2 * M <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        end = now + rem / (len(cands) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            S = search(MT, inv, M, end, rng)
            if S is None:
                continue
            n, edges = to_edges(MT, M, S)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue

    if best is not None:
        return best
    return trivial(d, D)
