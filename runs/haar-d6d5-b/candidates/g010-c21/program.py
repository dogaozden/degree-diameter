"""Haar-graph search over larger non-abelian groups for the (d=6, D=5) target.

CONSTRUCTION.  Take a finite group G of order N and a connection set S with |S| = d.
Vertices A_g = g and B_g = N + g.  Edges A_g ~ B_{s*g} for s in S.  The graph is bipartite,
d-regular, and has 2N vertices.  By the Haar criterion, diameter <= 5 holds whenever
(S^-1 S)^2 = G and (S S^-1)^2 = G.  Left-translating S does not change the cost, so we fix
the identity in S.

SEARCH.  For each candidate group (metacyclic Z_m x|_lam Z_k and Heis(3) x Z_k, of order
343..440) we run simulated annealing over S, minimising the number of uncovered elements.
Groups are visited round-robin in ascending order, and any group whose graph would not beat
the current best is skipped.  Every returned graph is checked with lib.is_valid.

FALLBACK.  A verified 660-vertex Haar graph, then a small trivial graph for other cases.
"""
import math
import time
from math import gcd

import numpy as np

import lib


TARGET = (6, 5)
SLICE = 1.2


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, with (a, j)(b, l) = (a + lam^j b, j + l)."""
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


def group_list(lo, hi):
    """Specs (order, spec) of non-abelian candidate groups with order in [lo, hi]."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((N, ("meta", m, k, lam)))
                    cnt += 1
                    if cnt >= 2:
                        break
    for k in range(13, 17):
        N = 27 * k
        if lo <= N <= hi:
            out.append((N, ("heis", k)))
    out.sort(key=lambda t: t[0])
    return out


def build_group(spec):
    if spec[0] == "meta":
        return group_meta(spec[1], spec[2], spec[3])
    return group_times_cyclic(group_heis3(), spec[1])


# ----------------------------------------------------------------------------- search

def make_cost(MT, inv, N):
    """Cost of S = number of uncovered elements in (S^-1 S)^2 and (S S^-1)^2.  0 means valid."""
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


def anneal(MT, inv, N, d, deadline, rng, T=0.8, patience=4000):
    """Anneal over S (identity fixed in S) with random restarts.  Returns S with cost 0, or None."""
    cost = make_cost(MT, inv, N)
    while time.monotonic() < deadline:
        others = rng.choice(np.arange(1, N), size=d - 1, replace=False)
        S = np.concatenate(([0], others)).astype(np.int64)
        cur = cost(S)
        since = 0
        while since < patience:
            if cur == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            i = int(rng.integers(1, d))
            x = int(rng.integers(1, N))
            if x in S:
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
    return None


def haar_edges(MT, N, S):
    """Edges of the Haar graph: A_g = g, B_g = N + g, A_g ~ B_{s*g} for s in S."""
    edges = []
    for s in S:
        row = MT[int(s)]
        for g in range(N):
            edges.append((g, N + int(row[g])))
    return 2 * N, edges


# ----------------------------------------------------------------------------- fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Verified 660-vertex Haar graph over group_meta(33, 10, 26)."""
    MT, _ = group_meta(33, 10, 26)
    N = MT.shape[0]
    return haar_edges(MT, N, FALLBACK_S)


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
    budget = max(1.0, min(0.75 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        best = None

    specs = group_list(343, 440)
    while time.monotonic() < deadline:
        best_n = best[0] if best is not None else 0
        active = [(N, s) for N, s in specs if 2 * N > best_n]
        if not active:
            break
        for N, spec in active:
            now = time.monotonic()
            if now >= deadline:
                break
            best_n = best[0] if best is not None else 0
            if 2 * N <= best_n:
                continue
            end = min(deadline, now + SLICE)
            try:
                MT, inv = build_group(spec)
                S = anneal(MT, inv, N, d, end, rng)
                if S is not None:
                    n, edges = haar_edges(MT, N, S)
                    if n > best_n and lib.is_valid(n, edges, d, D):
                        best = (n, edges)
            except Exception:
                continue

    if best is not None:
        return best
    return trivial(d, D)
