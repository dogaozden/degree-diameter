"""Haar-graph search for the (d=6, D=5) target, with a verified fallback.

CONSTRUCTION (replaces the parent's two-orbit lifts).
Take a group G of order M and a 6-element set S in G. Vertices are A_g = g and B_g = M + g.
Edges: A_g ~ B_{s*g} for s in S. The graph is bipartite, 6-regular, with 2M vertices.
Right multiplication by h (A_g -> A_{gh}, B_x -> B_{xh}) is an automorphism, so each side is
transitive. The diameter is at most 5 iff
    (S^-1 S)^2 = G   (A-side cover from A_e within 4 steps) and
    (S S^-1)^2 = G   (B-side cover from B_e within 4 steps).
cost(S) counts the uncovered elements of both sets. Simulated annealing on S, round-robin over
non-abelian groups of order >= 343 (so 2M > 684), keeps the largest valid graph. Every result is
checked with lib.is_valid. If nothing is found, a checked 660-vertex Haar graph is returned.
"""
import math
import time
from math import gcd

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p (order p^3): (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b'), element a*p*p + b*p + c."""
    N = p ** 3
    e = np.arange(N, dtype=np.int64)
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


# ----------------------------------------------------------------------------- search

def make_cost(MT, inv, M):
    """Return cost(S): uncovered elements of (S^-1 S)^2 and (S S^-1)^2 in G (0 means diameter <= 5)."""
    def cost(S):
        iS = inv[S]
        P = MT[iS[:, None], S[None, :]].ravel()          # s^-1 t
        Q = MT[P[:, None], P[None, :]].ravel()
        c1 = M - np.unique(Q).size
        P2 = MT[S[:, None], iS[None, :]].ravel()         # s t^-1
        Q2 = MT[P2[:, None], P2[None, :]].ravel()
        c2 = M - np.unique(Q2).size
        return c1 + c2
    return cost


def anneal(MT, inv, M, deadline, rng, T0=0.8, patience=3000):
    """Anneal a DEG-subset S with cost 0, restarting when stuck. Returns S (int64 array) or None."""
    cost = make_cost(MT, inv, M)
    while time.monotonic() < deadline:
        S = rng.choice(M, DEG, replace=False).astype(np.int64)
        cur = cost(S)
        since = 0
        while since < patience:
            if cur == 0:
                return S
            if time.monotonic() >= deadline:
                break
            i = int(rng.integers(DEG))
            x = int(rng.integers(M))
            if x in S:
                since += 1
                continue
            S2 = S.copy()
            S2[i] = x
            c2 = cost(S2)
            dlt = c2 - cur
            if dlt <= 0 or rng.random() < math.exp(-dlt / T0):
                S = S2
                cur = c2
                since = 0 if dlt < 0 else since + 1
            else:
                since += 1
        if cur == 0:
            return S
    return None


# ----------------------------------------------------------------------------- candidates

def candidates():
    """Non-abelian groups of order 343..420, sorted by order, as (order, builder) pairs."""
    items = []
    for N in range(343, 421):
        if N == 343:
            items.append((343, lambda: group_heis(7)))
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = next((l for l in range(2, m) if gcd(l, m) == 1 and pow(l, k, m) == 1), None)
            if lam is None:
                continue
            items.append((N, lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    for k in (13, 14, 15):
        items.append((27 * k, lambda k=k: group_times_cyclic(group_heis(3), k)))
    items.sort(key=lambda t: t[0])
    return items


def haar_edges(MT, S):
    """Edges of the Haar graph: A_g ~ B_{s*g}, with A_g = g and B_x = M + x."""
    M = MT.shape[0]
    edges = []
    for s in S.tolist():
        row = MT[s]
        for g in range(M):
            edges.append((g, M + int(row[g])))
    return edges


# ----------------------------------------------------------------------------- fallbacks

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
    budget = max(1.0, min(0.75 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates()[:24]
    best = None
    best_M = 0
    slice_t = 2.0
    progress = True
    while progress and time.monotonic() < deadline:
        progress = False
        for M, builder in cands:
            if M <= best_M:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + slice_t)
            try:
                MT, inv = builder()
                Mg = MT.shape[0]
                S = anneal(MT, inv, Mg, end, rng)
                progress = True
                if S is None:
                    continue
                edges = haar_edges(MT, S)
                n = 2 * Mg
                if Mg > best_M and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_M = Mg
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
