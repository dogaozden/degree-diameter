"""Haar graphs over non-abelian groups for the (d=6, D=5) target, with a verified fallback.

CONSTRUCTION.  For a group G of order N (multiplication table MT, identity 0) and a 6-subset S of G, the
Haar graph has A-vertices g and B-vertices N+g, with edges g ~ N + s*g for s in S.  It is bipartite,
6-regular, and has 2N vertices.  Right multiplication by any h is an automorphism, so the diameter is at
most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  The search minimises the number of uncovered elements of
those two sets (cost 0 means valid).

SEARCH.  Simulated annealing over S with random restarts, over several non-abelian metacyclic groups and
Heis(3) x Z_k, with orders in [331, 420].  Any valid result of order N beats the 660-vertex fallback
(2N > 660).  Once a result is found, only larger groups are tried.  Every returned graph is checked with
lib.is_valid.  If nothing is found, the checked 660-vertex Haar graph is returned.
"""
import math
import time
from math import gcd

import numpy as np

import lib


TARGET = (6, 5)
K_SET = 6


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


def group_heis3():
    """Heisenberg group mod 3 (order 27), element (a, b, c) -> a*9 + b*3 + c, identity 0."""
    p = 3
    e = np.arange(p ** 3, dtype=np.int64)
    A, B, C = e // 9, (e // 3) % 3, e % 3
    Ap = (A[:, None] + A[None, :]) % p
    Bp = (B[:, None] + B[None, :]) % p
    Cp = (C[:, None] + C[None, :] + A[:, None] * B[None, :]) % p
    return _finish(Ap * 9 + Bp * 3 + Cp)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    C = (np.arange(k)[:, None] + np.arange(k)[None, :]) % k
    MT4 = MT0[:, None, :, None] * k + C[None, :, None, :]
    return _finish(MT4.reshape(n0 * k, n0 * k))


def candidates(lo=331, hi=420):
    """Non-abelian groups of order in [lo, hi]: metacyclic Z_m x| Z_k (up to 2 actions per (m,k)) plus Heis(3) x Z_k."""
    out = []
    for m in range(3, hi + 1):
        for k in range(2, hi // m + 1):
            n_ = m * k
            if n_ < lo or n_ > hi:
                continue
            found = 0
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((n_, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
                    found += 1
                    if found >= 2:
                        break
    for k in (13, 14):
        n_ = 27 * k
        if lo <= n_ <= hi:
            out.append((n_, (lambda k=k: group_times_cyclic(group_heis3(), k))))
    out.sort(key=lambda t: t[0])
    return out


# ------------------------------------------------------------------------ search

def cost_of(MT, inv, N, S):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2 in G.  0 means the Haar graph has diameter <= 5."""
    iS = inv[S]
    P1 = np.unique(MT[iS[:, None], S[None, :]])
    V1 = MT[P1[:, None], P1[None, :]].ravel()
    m1 = np.zeros(N, dtype=bool)
    m1[V1] = True
    P2 = np.unique(MT[S[:, None], iS[None, :]])
    V2 = MT[P2[:, None], P2[None, :]].ravel()
    m2 = np.zeros(N, dtype=bool)
    m2[V2] = True
    return 2 * N - int(m1.sum()) - int(m2.sum())


def anneal(MT, inv, N, deadline, rng, T=1.0, patience=5000):
    """Annealing over 6-subsets S with random restarts.  Returns a cost-0 S, or None at the deadline."""
    k = K_SET
    while time.monotonic() < deadline:
        S = rng.choice(N, k, replace=False).astype(np.int64)
        cur = cost_of(MT, inv, N, S)
        best_here = cur
        since = 0
        while since < patience:
            if cur == 0:
                return S.copy()
            if time.monotonic() >= deadline:
                return None
            i = int(rng.integers(k))
            x = int(rng.integers(N))
            if np.any(S == x):
                continue
            old = S[i]
            S[i] = x
            c2 = cost_of(MT, inv, N, S)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                if cur < best_here:
                    best_here = cur
                    since = 0
                else:
                    since += 1
            else:
                S[i] = old
                since += 1
        if cur == 0:
            return S.copy()
    return None


def haar_edges(MT, N, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex is N+g, edge g ~ N + s*g for s in S."""
    g = np.arange(N, dtype=np.int64)
    E = []
    for s in S.tolist():
        nb = (N + MT[s, g]).tolist()
        E.extend(zip(g.tolist(), nb))
    return 2 * N, [(int(a), int(b)) for a, b in E]


# ------------------------------------------------------------------------ fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Valid 660-vertex Haar graph over group_meta(33, 10, 26)."""
    MT, _ = group_meta(33, 10, 26)
    N = MT.shape[0]
    return haar_edges(MT, N, np.array(FALLBACK_S, dtype=np.int64))


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

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates()
    cache = {}
    best = None  # (n, edges, group_order)

    while True:
        if deadline - time.monotonic() < 0.5:
            break
        best_order = best[2] if best is not None else 0
        pool = [i for i, (n_, _) in enumerate(cands) if n_ > best_order]
        if not pool:
            break
        idx = pool[int(rng.integers(len(pool)))]
        _, builder = cands[idx]
        try:
            if idx not in cache:
                cache[idx] = builder()
            MT, inv = cache[idx]
            N = MT.shape[0]
            slice_end = min(deadline, time.monotonic() + 2.0)
            S = anneal(MT, inv, N, slice_end, rng)
            if S is not None:
                n, edges = haar_edges(MT, N, S)
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges, N)
        except Exception:
            continue

    if best is not None:
        return best[0], best[1]
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
