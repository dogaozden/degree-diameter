"""Haar-graph search for the (d=6, D=5) target, with a verified fallback.

CONSTRUCTION.  Take a finite group G of order N and a 6-element set S of G.  The Haar graph
H(G, S) has vertices A_g = g and B_g = N + g, with edges A_g ~ B_{s*g} for s in S.  It is bipartite,
6-regular, and has 2N vertices.

EXACT CRITERION.  Let T = S^-1 S and U = S S^-1.  Then A-to-A distances are governed by T^2, B-to-B
distances by U^2, and A-to-B distances by S*T^2 = U^2*S.  So diameter <= 5 holds iff T^2 = G and U^2 = G.
COST = (N - |T^2|) + (N - |U^2|), and cost 0 means valid.

SEARCH.  Simulated annealing over S with single-slot replacements, random restarts, and candidate groups
of order 331 upward (non-abelian metacyclic groups, plus Heisenberg(3) x Z_k).  Any group of order
N >= 331 gives a graph with 2N >= 662 vertices.  The best result is re-checked with lib.is_valid.
If nothing valid is found, a checked 660-vertex Haar graph is returned.
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


# ------------------------------------------------------------------------ Haar search

K_SET = 6
PATIENCE = 2500
TEMP = 1.0


def cover_cost(MT, inv, S):
    """Uncovered elements of T^2 and U^2 (T = S^-1 S, U = S S^-1).  0 means diameter <= 5."""
    N = MT.shape[0]
    iS = inv[S]
    T = MT[iS[:, None], S[None, :]].ravel()
    U = MT[S[:, None], iS[None, :]].ravel()
    total = 0
    for W in (T, U):
        mark = np.zeros(N, dtype=bool)
        mark[MT[W[:, None], W[None, :]].ravel()] = True
        total += N - int(np.count_nonzero(mark))
    return total


def anneal(MT, inv, N, deadline, rng):
    """Annealing over connection sets with random restarts.  Returns a sorted list S with cost 0, or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, K_SET, replace=False).astype(np.int64)
        cur = cover_cost(MT, inv, S)
        since = 0
        while since < PATIENCE:
            if cur == 0:
                return sorted(int(x) for x in S)
            if time.monotonic() >= deadline:
                return None
            k = int(rng.integers(K_SET))
            x = int(rng.integers(N))
            if x in S:
                since += 1
                continue
            old = int(S[k])
            S[k] = x
            c2 = cover_cost(MT, inv, S)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                S[k] = old
                since += 1
    return None


def haar_edges(MT, S):
    """Edges of H(G, S): A_g = g joined to B_{s*g} = N + s*g."""
    N = MT.shape[0]
    g = np.arange(N, dtype=np.int64)
    E = []
    for s in S:
        v = MT[int(s), g]
        E.extend(zip(g.tolist(), (N + v).tolist()))
    return 2 * N, [(int(a), int(b)) for a, b in E]


def candidates(lo=331, hi=400, cap=20):
    """Non-abelian metacyclic groups of order lo..hi (one per order), plus Heis(3) x Z_k, sorted by order."""
    out = []
    for N in range(lo, hi + 1):
        pick = None
        for m in range(3, N):
            if N % m:
                continue
            k = N // m
            if k < 2:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    pick = (m, k, lam)
                    break
            if pick:
                break
        if pick:
            m, k, lam = pick
            out.append((N, lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    out.append((351, lambda: group_times_cyclic(group_heis3(), 13)))
    out.append((378, lambda: group_times_cyclic(group_heis3(), 14)))
    out.sort(key=lambda t: t[0])
    return out[:cap]


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
    budget = max(2.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates()
    best = None
    for idx, (N, builder) in enumerate(cands):
        if best is not None and 2 * N <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        end = now + rem / (len(cands) - idx)
        try:
            MT, inv = builder()
            S = anneal(MT, inv, MT.shape[0], end, rng)
            if S is None:
                continue
            n, edges = haar_edges(MT, S)
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
