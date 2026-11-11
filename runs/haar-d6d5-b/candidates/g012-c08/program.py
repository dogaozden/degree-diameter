"""Haar-graph search over non-abelian groups of order 342 and up, with a verified fallback.

CONSTRUCTION.  Take a group G of order N and a 6-element set S of G.  Vertices (g, A) and (g, B) get ids
g and N + g.  Edges (g, A) ~ (s*g, B) for s in S.  The graph is bipartite and 6-regular with 2N vertices.
Right multiplication by h is an automorphism that is transitive on each side, so diameter <= 5 holds iff
the radius-5 balls around (e, A) and (e, B) both cover all 2N vertices.  COST = total uncovered vertices
for those two balls (0 = valid).

CANDIDATE GROUPS.  AGL(1,19) = Z_19 x| Z_18 (order 342, the record order), Heis(7) (order 343), and
metacyclic Z_m x| Z_k with orders 343..360.  The biggest graph wins, and every candidate is checked with
lib.is_valid before it is accepted.

SEARCH.  Simulated annealing over S with random restarts.  Moves replace one element of S by a random
element or by a quotient s_i * s_j^-1.

FALLBACK.  If nothing valid is found, the verified 660-vertex Haar graph is returned, and then a trivial
graph for any other case.
"""
import math
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p (order p^3): (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b'), index a*p^2 + b*p + c."""
    e = np.arange(p ** 3, dtype=np.int64)
    A, B, C = e // (p * p), (e // p) % p, e % p
    Ap = (A[:, None] + A[None, :]) % p
    Bp = (B[:, None] + B[None, :]) % p
    Cp = (C[:, None] + C[None, :] + A[:, None] * B[None, :]) % p
    return _finish(Ap * p * p + Bp * p + Cp)


# ------------------------------------------------------------------------ Haar search

def make_nbr(MT, inv, N, S):
    """Neighbour table (2N x 6).  A-vertex g ~ N + s*g; B-vertex h ~ s^-1 * h."""
    S = np.asarray(S, dtype=np.int64)
    A = MT[S].T + N
    B = MT[inv[S]].T
    return np.vstack([A, B])


def cover(nbr, src, V):
    """Number of vertices within distance 5 of src."""
    vis = np.zeros(V, dtype=bool)
    vis[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(5):
        nb = nbr[front].ravel()
        nb = nb[~vis[nb]]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        vis[nb] = True
        front = nb
    return int(vis.sum())


def cost(MT, inv, N, S):
    """Uncovered vertices from the two side representatives (e, A) and (e, B).  0 means diameter <= 5."""
    V = 2 * N
    nbr = make_nbr(MT, inv, N, S)
    return (V - cover(nbr, 0, V)) + (V - cover(nbr, N, V))


def anneal(MT, inv, N, deadline, rng, patience=3000, T=1.5):
    """Annealing over 6-element sets S with restarts.  Returns a valid S (cost 0) or None."""
    while time.monotonic() < deadline:
        S = [int(x) for x in rng.choice(N, 6, replace=False)]
        cur = cost(MT, inv, N, S)
        since = 0
        while since < patience:
            if cur == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            k = int(rng.integers(6))
            if rng.random() < 0.5:
                x = int(rng.integers(N))
            else:
                x = int(MT[S[int(rng.integers(6))], inv[S[int(rng.integers(6))]]])
            if x in S:
                since += 1
                continue
            S2 = S.copy()
            S2[k] = x
            c2 = cost(MT, inv, N, S2)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = S2, c2
                since = 0 if delta < 0 else since + 1
            else:
                since += 1
        if cur == 0:
            return S
    return None


def to_edges(MT, S):
    """Edge list of the Haar graph over MT with connection set S: (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    gs = list(range(N))
    E = []
    for s in S:
        E.extend(zip(gs, (N + MT[s]).tolist()))
    return 2 * N, E


# ------------------------------------------------------------------------ candidates

def candidates():
    """AGL(1,19) (order 342), Heis(7) (343), then metacyclic groups of orders 343..360, sorted by order."""
    out = [(342, lambda: group_meta(19, 18, 2))]
    out.append((343, lambda: group_heis(7)))
    meta = []
    for m in range(3, 361):
        for k in range(2, 361 // m + 1):
            n_ = m * k
            if n_ < 343 or n_ > 360:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    meta.append((n_, m, k, lam))
                    break
    meta.sort()
    for n_, m, k, lam in meta:
        out.append((n_, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    return out[:14]


# ------------------------------------------------------------------------ fallback

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


# ------------------------------------------------------------------------ entry point

TARGET = (6, 5)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates()
    best = None
    for idx, (order, builder) in enumerate(cands):
        if best is not None and 2 * order <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.3:
            break
        end = now + rem / (len(cands) - idx)
        try:
            MT, inv = builder()
            N = MT.shape[0]
            S = anneal(MT, inv, N, end, rng)
            if S is None:
                continue
            n, edges = to_edges(MT, S)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue
    if best is not None:
        return best
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
