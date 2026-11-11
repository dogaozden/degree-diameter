"""Haar-graph search over non-abelian groups of order 343..~365 for the (d=6, D=5) target.

Haar graph H(G, S): vertices A_g and B_g for g in G, edges A_g ~ B_{s*g} for s in S, |S| = d.
It is bipartite, d-regular, and has 2|G| vertices. Diameter <= 5 holds whenever
(S^-1 S)^2 = G and (S S^-1)^2 = G. This is sufficient, and cost = uncovered elements.
Replacing S by x*S gives an isomorphic graph, so S can be normalised to contain the identity.
Order 2|G| > 684 needs |G| >= 343. Every result is checked with lib.is_valid, with a
verified 660-vertex Haar fallback and then a trivial graph as backstops.
"""
import math
import time
from math import gcd

import numpy as np

import lib


TARGET = (6, 5)


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
    """Heisenberg group mod odd prime p (order p^3), element (a, b, c) -> a*p*p + b*p + c, identity 0."""
    N = p ** 3
    e = np.arange(N, dtype=np.int64)
    A, B, C = e // (p * p), (e // p) % p, e % p
    Ap = (A[:, None] + A[None, :]) % p
    Bp = (B[:, None] + B[None, :]) % p
    Cp = (C[:, None] + C[None, :] + A[:, None] * B[None, :]) % p
    return _finish(Ap * p * p + Bp * p + Cp)


# ------------------------------------------------------------------------- Haar search

def make_cost(MT, inv, n):
    """Cost of S: uncovered elements of (S^-1 S)^2 and (S S^-1)^2. Zero means diameter <= 5."""
    def cost_fn(S):
        Si = inv[S]
        T = np.unique(MT[Si[:, None], S[None, :]])        # s^-1 t
        P = MT[T[:, None], T[None, :]]                    # (S^-1 S)^2
        m1 = np.zeros(n, dtype=bool)
        m1[P.ravel()] = True
        U = np.unique(MT[S[:, None], Si[None, :]])        # s t^-1
        Q = MT[U[:, None], U[None, :]]                    # (S S^-1)^2
        m2 = np.zeros(n, dtype=bool)
        m2[Q.ravel()] = True
        return 2 * n - int(m1.sum()) - int(m2.sum())
    return cost_fn


def anneal(cost_fn, n, d, deadline, rng):
    """Simulated annealing over S (identity fixed in slot 0) with random restarts. Returns S or None."""
    while time.monotonic() < deadline:
        T = float(rng.choice([0.6, 1.0, 1.5]))
        S = np.empty(d, dtype=np.int64)
        S[0] = 0
        S[1:] = rng.choice(np.arange(1, n, dtype=np.int64), d - 1, replace=False)
        cur = cost_fn(S)
        stall = 0
        while stall < 4000:
            if cur == 0:
                return S.copy()
            if time.monotonic() >= deadline:
                return None
            i = int(rng.integers(1, d))
            x = int(rng.integers(1, n))
            if x in S:
                stall += 1
                continue
            old = int(S[i])
            S[i] = x
            c2 = cost_fn(S)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                stall = 0 if delta < 0 else stall + 1
            else:
                S[i] = old
                stall += 1
    return None


def candidates(max_cands=14):
    """Groups of order 343 (Heis(7), Z_49 x| Z_7) then one non-abelian metacyclic group per order 344..400."""
    out = [
        (343, lambda: group_heis(7)),
        (343, lambda: group_meta(49, 7, 8)),
    ]
    for n_ in range(344, 401):
        for k in range(2, n_):
            if n_ % k:
                continue
            m = n_ // k
            if m < 3:
                continue
            lams = [lam for lam in range(2, m) if gcd(lam, m) == 1 and pow(lam, k, m) == 1]
            if lams:
                lam = lams[0]
                out.append((n_, lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
                break
    return out[:max_cands]


def haar_edges(MT, N, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N + g; A_g ~ B_{s g}."""
    edges = [(g, N + int(MT[int(s), g])) for s in S for g in range(N)]
    return 2 * N, edges


# ------------------------------------------------------------------------ fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Valid 660-vertex Haar graph (group_meta(33, 10, 26))."""
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


# ------------------------------------------------------------------------ entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates()
    cache = {}
    best = None  # (order, S, MT)
    slice_len = 0.4
    while time.monotonic() < deadline - 0.2:
        ran = False
        for idx, (order, builder) in enumerate(cands):
            if best is not None and order <= best[0]:
                continue
            now = time.monotonic()
            if now >= deadline - 0.2:
                break
            end = min(deadline, now + slice_len)
            try:
                if idx not in cache:
                    MT, inv = builder()
                    cache[idx] = (MT, make_cost(MT, inv, order))
                MT, cf = cache[idx]
                ran = True
                S = anneal(cf, order, d, end, rng)
            except Exception:
                continue
            if S is not None:
                best = (order, S, MT)
        if not ran:
            break
        slice_len *= 2

    if best is not None:
        try:
            order, S, MT = best
            n, edges = haar_edges(MT, order, S)
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
