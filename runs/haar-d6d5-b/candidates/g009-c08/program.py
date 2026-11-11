"""Haar-graph search over larger non-abelian groups for the (d=6, D=5) target.

CONSTRUCTION.  A Haar graph on a group G of order N with connection set S (|S| = 6) has
vertices A_g and B_g (ids g and N+g) and edges A_g ~ B_{s*g} for s in S.  It is 6-regular and
bipartite on 2N vertices.  With the identity in S (WLOG, by relabelling B), diameter <= 5 holds
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  So COST = uncovered elements in those two squares, and
COST 0 gives a valid graph with 2N vertices.

GROUPS.  Heisenberg mod 7 (order 343, so 2N = 686 > 684) first, then non-abelian metacyclic
groups Z_m x| Z_k of orders 344..360.

SEARCH.  Simulated annealing over the five non-identity elements of S, with restarts.  Each
returned set is checked with lib.is_valid.  If nothing beats the fallback, a checked 660-vertex
Haar graph is returned.
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
    """Heisenberg group mod p (order p^3): (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b').  Identity is index 0."""
    e = np.arange(p ** 3, dtype=np.int64)
    A, B, C = e // (p * p), (e // p) % p, e % p
    Ap = (A[:, None] + A[None, :]) % p
    Bp = (B[:, None] + B[None, :]) % p
    Cp = (C[:, None] + C[None, :] + A[:, None] * B[None, :]) % p
    return _finish(Ap * p * p + Bp * p + Cp)


# ------------------------------------------------------------------------ Haar search

def cost(MT, inv, N, S):
    """Uncovered elements in (S^-1 S)^2 and (S S^-1)^2.  0 means diameter <= 5 (S contains identity)."""
    Sinv = inv[S]
    Q = MT[Sinv[:, None], S[None, :]].ravel()
    P = MT[S[:, None], Sinv[None, :]].ravel()
    total = 0
    for R in (Q, P):
        R = np.unique(R)
        R2 = MT[R[:, None], R[None, :]].ravel()
        mark = np.zeros(N, dtype=bool)
        mark[R2] = True
        total += N - int(mark.sum())
    return total


def search(MT, inv, N, deadline, rng, k=6, T=1.0, patience=3000):
    """Anneal S = {0} + 5 other elements until cost 0 or the deadline.  Returns S (ndarray) or None."""
    while time.monotonic() < deadline:
        pool = rng.choice(N - 1, size=k - 1, replace=False) + 1
        S = [0] + [int(x) for x in pool]
        cur = cost(MT, inv, N, np.array(S, dtype=np.int64))
        since = 0
        while since < patience:
            if cur == 0:
                return np.array(S, dtype=np.int64)
            if time.monotonic() >= deadline:
                break
            i = 1 + int(rng.integers(k - 1))
            x = int(rng.integers(1, N))
            if x in S:
                since += 1
                continue
            old = S[i]
            S[i] = x
            c2 = cost(MT, inv, N, np.array(S, dtype=np.int64))
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                S[i] = old
                since += 1
        if cur == 0:
            return np.array(S, dtype=np.int64)
    return None


def haar_edges(MT, N, S):
    """Return (2N, edges) for the Haar graph A_g ~ B_{s g}, A = g, B = N + g."""
    edges = []
    for s in S.tolist():
        row = MT[s].tolist()
        edges.extend((g, N + row[g]) for g in range(N))
    return 2 * N, edges


# ------------------------------------------------------------------------ candidates

def candidates():
    """Heis(7) (order 343) first, then one non-abelian metacyclic group per (m, k), orders 344..360."""
    out = [(343, lambda: group_heis(7))]
    for n in range(344, 361):
        for m in range(2, n):
            if n % m:
                continue
            k = n // m
            if k < 2:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((n, lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
                    break
    return out[:10]


# ------------------------------------------------------------------------ fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Valid 660-vertex Haar graph (group_meta(33, 10, 26)), checked before return."""
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
    budget = max(2.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates()
    best = None
    for idx, (n_, builder) in enumerate(cands):
        if best is not None and 2 * n_ <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        end = now + rem / (len(cands) - idx)
        try:
            MT, inv = builder()
            N = MT.shape[0]
            S = search(MT, inv, N, end, rng)
            if S is None:
                continue
            n, edges = haar_edges(MT, N, S)
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
