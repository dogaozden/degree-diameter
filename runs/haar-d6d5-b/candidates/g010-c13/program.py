"""Haar-graph search for the (d=6, D=5) target, replacing the two-orbit lift.

CONSTRUCTION.  Take a group G of order M and a connection set S of 6 distinct elements.
Vertices are A-vertex g (id g) and B-vertex g (id M+g), with edges (g,A) ~ (s*g,B) for s in S.
The graph is bipartite, 6-regular, and has 2M vertices.  It has diameter <= 5 exactly when
(S^-1 S)^2 = G and (S S^-1)^2 = G.  Each candidate S has cost = uncovered elements in those two
sets, and cost 0 means valid.

GROUPS.  Non-abelian groups of order 343..380: metacyclic Z_m x| Z_k, plus the Heisenberg group
mod 7 (order 343).  A valid graph beats the record 684 once 2M >= 686, so M >= 343.

SEARCH.  Simulated annealing over S with single-element replacement and random restarts.  Each
candidate group gets an equal share of the remaining budget.  Any result is checked with
lib.is_valid.  If nothing valid is found, the checked 660-vertex Haar fallback is returned.
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
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p (order p^3), element (a, b, c) -> a*p*p + b*p + c, identity 0."""
    e = np.arange(p ** 3, dtype=np.int64)
    A, B, C = e // (p * p), (e // p) % p, e % p
    Ap = (A[:, None] + A[None, :]) % p
    Bp = (B[:, None] + B[None, :]) % p
    Cp = (C[:, None] + C[None, :] + A[:, None] * B[None, :]) % p
    return _finish(Ap * p * p + Bp * p + Cp)


def make_cost(MT, inv, N):
    """Return cost(S): uncovered elements of (S^-1 S)^2 and (S S^-1)^2.  0 means diameter <= 5."""
    def cost(S):
        Si = inv[S]
        P1 = MT[Si[:, None], S[None, :]].ravel()
        Q1 = MT[P1[:, None], P1[None, :]].ravel()
        m1 = np.zeros(N, dtype=bool)
        m1[Q1] = True
        P2 = MT[S[:, None], Si[None, :]].ravel()
        Q2 = MT[P2[:, None], P2[None, :]].ravel()
        m2 = np.zeros(N, dtype=bool)
        m2[Q2] = True
        return 2 * N - int(m1.sum()) - int(m2.sum())
    return cost


# ------------------------------------------------------------------------ candidates

def candidates(lo=343, hi=380):
    """Non-abelian groups of order lo..hi: Heis(7) first, then metacyclic groups, sorted by order."""
    out = [(343, lambda: group_heis(7))]
    for N_ in range(lo, hi + 1):
        found = 0
        for m in range(2, N_):
            if N_ % m:
                continue
            k = N_ // m
            if k < 2:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((N_, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
                    found += 1
                    break
            if found >= 2:
                break
    out.sort(key=lambda t: t[0])
    return out[:30]


# ------------------------------------------------------------------------ annealing

def anneal(cost, N, d, deadline, rng):
    """Anneal a d-subset S of G with cost 0.  Returns S as an int64 array, or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, size=d, replace=False).astype(np.int64)
        cur = cost(S)
        T = 0.7
        since = 0
        while since < 3000 and time.monotonic() < deadline:
            if cur == 0:
                return S
            i = int(rng.integers(d))
            x = int(rng.integers(N))
            if np.any(S == x):
                since += 1
                continue
            old = S[i]
            S[i] = x
            c2 = cost(S)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                S[i] = old
                since += 1
        if cur == 0:
            return S
    return None


def to_edges(N, MT, S):
    """Haar graph edges: A-vertex g is g, B-vertex g is N + g, edge (g,A) ~ (s*g,B)."""
    g = np.arange(N, dtype=np.int64)
    edges = []
    for s in S.tolist():
        v = N + MT[s, g]
        edges.extend((int(a), int(b)) for a, b in zip(g.tolist(), v.tolist()))
    return 2 * N, edges


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
    budget = max(1.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates()
    best = None
    for idx, (N_, builder) in enumerate(cands):
        if best is not None and 2 * N_ <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        end = now + rem / (len(cands) - idx)
        try:
            MT, inv = builder()
            N = MT.shape[0]
            S = anneal(make_cost(MT, inv, N), N, d, end, rng)
            if S is None:
                continue
            n, edges = to_edges(N, MT, S)
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
