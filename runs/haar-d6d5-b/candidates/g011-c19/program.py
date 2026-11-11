"""Haar-graph search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

CONSTRUCTION.  Take a finite group G of order N and a 6-element set S.  The Haar graph H(G, S) has vertices
A_g and B_g (g in G) and edges A_g ~ B_{s*g} for s in S.  It is bipartite, 6-regular, and has 2N vertices.

DIAMETER CRITERION (Haar graphs, diameter <= 5).  Let P = S^-1 S and Q = S S^-1.  Then
  * A-to-A distances <= 4 cover G iff (S^-1 S)^2 = G,
  * B-to-B distances <= 4 cover G iff (S S^-1)^2 = G,
  * A-to-B distances <= 5 cover G because S (S^-1 S)^2 = G whenever (S^-1 S)^2 = G.
So COST(S) = (N - |(S^-1 S)^2|) + (N - |(S S^-1)^2|) is 0 exactly when the graph has diameter <= 5.
The cost needs only 36-element and 1296-element products, so each evaluation is very cheap.

NEW IN THIS VERSION.  The earlier bi-Cayley search found nothing, so this version switches to Haar graphs over
groups of order 343..781 (2N > 684 beats the record).  The counting bound 1 + d(d-1) + d(d-1)^3 = 781 caps N.
Candidate groups: Heis(7) (order 343, exactly the threshold), Heis(3) x Z_k (order 27k), and metacyclic
Z_m x|_lam Z_k.  Each group gets an equal share of the search budget.  Simulated annealing replaces one set element
per move, with restarts when stuck.  Any found graph is checked with lib.is_valid.  If nothing is found, the valid
Haar graph of order 660 (checked at run time) or a trivial valid graph is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_N = 343        # 2 * 343 = 686 > 684 (record)
MAX_N = 781        # counting bound 1 + d(d-1) + d(d-1)^3 for d = 6


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------------- Haar helpers

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    g = np.arange(N)
    edges = []
    for s in S:
        row = MT[int(s)]
        edges.extend((int(a), N + int(row[a])) for a in g)
    return 2 * N, edges


def _cost(MT, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2 (0 means diameter <= 5)."""
    Si = inv[S]
    P1 = MT[Si[:, None], S[None, :]].ravel()
    Q1 = MT[P1[:, None], P1[None, :]].ravel()
    P2 = MT[S[:, None], Si[None, :]].ravel()
    Q2 = MT[P2[:, None], P2[None, :]].ravel()
    return ((N - np.count_nonzero(np.bincount(Q1, minlength=N)))
            + (N - np.count_nonzero(np.bincount(Q2, minlength=N))))


def _anneal(MT, inv, N, deadline, rng):
    """Anneal a 6-element set S until the Haar cost is 0; return a checked (n, edges) or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost(MT, inv, S, N)
        T = 0.5
        stall = 0
        while cur > 0 and stall < 3000 and time.monotonic() < deadline:
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if x in S:
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = _cost(MT, inv, newS, N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            n, edges = haar_edges(MT, S)
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _candidates():
    """Groups of order in [MIN_N, MAX_N]: Heis(7), Heis(3) x Z_k, and non-abelian metacyclic groups."""
    out = [("heis", 7, 0)]
    for k in (13, 14):
        out.append(("heis3k", 3, k))
    for NN in range(MIN_N, MAX_N + 1):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append(("meta", m, k, lam))
                    break
    return out


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    if c[0] == "heis":
        return group_heis(c[1])
    return group_times_cyclic(group_heis(c[1]), c[2])


# ------------------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        n, edges = haar_edges(MT, [0, 179, 116, 180, 47, 306])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = _candidates()
    best = None
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = _make(c)
            N = MT.shape[0]
            g = _anneal(MT, inv, N, end, rng)
        except Exception:
            continue
        if g is not None and (best is None or g[0] > best[0]):
            best = g
            break  # any valid graph beating the record is enough; stop early
    if best is not None:
        return best
    return _fallback(d, D)
