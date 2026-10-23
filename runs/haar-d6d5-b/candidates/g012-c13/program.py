"""Haar-graph search over non-abelian groups for the (d=6, D=5) target.

CONSTRUCTION. For a group G of order M and a connection set S of size d, the Haar graph has
vertices A_g and B_g (g in G) and edges A_g ~ B_{s*g} for s in S. It is bipartite and d-regular
on 2M vertices. Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G, so the search
minimises cost(S) = (M - |(S^-1 S)^2|) + (M - |(S S^-1)^2|). A cost of 0 means the graph is valid.

SEARCH. Candidate groups are metacyclic Z_m x| Z_k of order 342..420, plus Heisenberg(7) and
Heisenberg(3) x Z_k. Each candidate gets short simulated-annealing slices in round-robin order.
Once a valid group is found, only larger groups are searched further. Every result is checked with
lib.is_valid. If nothing beats the fallback, the verified 660-vertex Haar graph is returned.
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
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    C = (np.arange(k)[:, None] + np.arange(k)[None, :]) % k
    MT4 = MT0[:, None, :, None] * k + C[None, :, None, :]
    return _finish(MT4.reshape(n0 * k, n0 * k))


# ------------------------------------------------------------------------ Haar search

def cost(MT, inv, S, M):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2 in G; 0 means diameter <= 5."""
    iS = inv[S]
    T1 = np.unique(MT[iS[:, None], S[None, :]])
    Q1 = np.unique(MT[T1[:, None], T1[None, :]])
    T2 = np.unique(MT[S[:, None], iS[None, :]])
    Q2 = np.unique(MT[T2[:, None], T2[None, :]])
    return (M - Q1.size) + (M - Q2.size)


def anneal(MT, inv, M, d, deadline, rng, patience=3000, T=1.0):
    """Simulated annealing over d-subsets S of G with random restarts. Returns S with cost 0, or None."""
    while time.monotonic() < deadline:
        S = rng.choice(M, size=d, replace=False).astype(np.int64)
        cur = cost(MT, inv, S, M)
        since = 0
        while since < patience and time.monotonic() < deadline:
            if cur == 0:
                return S
            i = int(rng.integers(d))
            x = int(rng.integers(M))
            if np.any(S == x):
                since += 1
                continue
            old = int(S[i])
            S[i] = x
            c2 = cost(MT, inv, S, M)
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


def haar_from(MT, S, M):
    """Haar graph: A-vertex g is g, B-vertex g is M + g; edges A_g ~ B_{s*g} for s in S."""
    V = MT[S, :]
    edges = [(g, M + int(V[i, g])) for i in range(len(S)) for g in range(M)]
    return 2 * M, edges


def candidates(lo, hi):
    """Non-abelian groups of order in [lo, hi], sorted by order: metacyclic, Heis(7), Heis(3) x Z_k."""
    out = []
    for k in range(2, hi + 1):
        for m in range(3, hi // k + 1):
            M = m * k
            if M < lo or M > hi:
                continue
            lams = [lam for lam in range(2, m) if gcd(lam, m) == 1 and pow(lam, k, m) == 1][:1]
            for lam in lams:
                out.append((M, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    if lo <= 343 <= hi:
        out.append((343, lambda: group_heis(7)))
    for k in (13, 14):
        M = 27 * k
        if lo <= M <= hi:
            out.append((M, (lambda k=k: group_times_cyclic(group_heis(3), k))))
    out.sort(key=lambda t: t[0])
    return out


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
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates(342, 420)
    best = None
    slice_len = min(3.0, max(0.5, budget / max(1, len(cands))))
    while time.monotonic() < deadline:
        progressed = False
        for M, builder in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            if best is not None and 2 * M <= best[0]:
                continue
            end = min(deadline, now + slice_len)
            try:
                MT, inv = builder()
                Mg = MT.shape[0]
                progressed = True
                S = anneal(MT, inv, Mg, d, end, rng)
                if S is not None:
                    n, edges = haar_from(MT, S, Mg)
                    if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                        best = (n, edges)
            except Exception:
                continue
        if not progressed:
            break
    if best is not None:
        return best
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
