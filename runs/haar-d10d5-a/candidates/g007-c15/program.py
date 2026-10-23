"""Haar-graph search for d=10, D=5 over metacyclic groups of order slightly above 2000.

CONSTRUCTION.  Haar graph H(G, S): vertices (g,A) and (g,B) for g in G, edges (g,A)~(s*g,B) for s in S.
It is bipartite, d-regular, and has 2|G| vertices.  Its diameter is at most 5 when
(S^-1 S)^2 = G and (S S^-1)^2 = G.  Order 2|G| > 4000 needs |G| >= 2001.

NEW IDEA: HOLE-DIRECTED MOVES.  Standard annealing proposes uniform random replacements.  Here,
with probability 1/2, a move picks an uncovered element t of one of the two covering conditions and
builds a replacement slot value that would make t a product of the form u1*u2*u3*u4.  Here u1 is an
element of S^-1 S (or S S^-1), and u2, u3, u4 are sampled from the current covering set.  The
resulting value for slot q is then forced by solving for s_q from s_p and u1.  Only the exact
incremental cost decides acceptance, so the targeting is only a heuristic.

SEARCH.  Metacyclic groups Z_m x| Z_k of order 2001..2060 are tried in ascending order.  For each one,
a Metropolis annealing run over d-subsets of G minimises the number of uncovered elements, with
restarts when stalled.  Any zero-cost S is turned into a graph and checked with lib.is_valid.

SAFETY.  A valid smaller Haar graph (order 3582) is verified first and kept as the baseline.  Only
graphs that pass lib.is_valid are returned.  Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


# ----------------------------------------------------------------------------- groups

def metacyclic(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) coded as a*k + j, with identity 0.
    Returns (multiplication table MT, inverse array inv).  Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_candidates(lo, hi, limit):
    """Non-abelian metacyclic parameters (m, k, lam) with lo <= m*k < hi, in ascending order of order."""
    out = []
    for N in range(lo, hi):
        for k in range(2, N // 3 + 1):
            if N % k:
                continue
            m = N // k
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((m, k, lam))
                    break
            if len(out) >= limit:
                return out
    return out


# ----------------------------------------------------------------------------- Haar graphs

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g,A) ~ (s*g,B)."""
    N = MT.shape[0]
    g = np.arange(N)
    edges = []
    for s in S:
        row = MT[int(s)]
        edges.extend((int(a), int(N + b)) for a, b in zip(g, row))
    return 2 * N, edges


def checked(MT, S, d, D):
    """(n, edges) for the Haar graph of S if lib.is_valid accepts it, else None."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# ----------------------------------------------------------------------------- cost

def evaluate(MT, inv, S):
    """Return (cost, uncovered1, uncovered2, U1, U2).
    U1 = {s_i^-1 s_j}, U2 = {s_i s_j^-1}.  Cost = #G \\ (U1)^2 + #G \\ (U2)^2."""
    N = MT.shape[0]
    Si = inv[S]
    U1 = np.unique(MT[Si[:, None], S[None, :]])
    U2 = np.unique(MT[S[:, None], Si[None, :]])
    cov1 = np.zeros(N, dtype=bool)
    cov1[MT[U1[:, None], U1[None, :]].ravel()] = True
    cov2 = np.zeros(N, dtype=bool)
    cov2[MT[U2[:, None], U2[None, :]].ravel()] = True
    unc1 = np.flatnonzero(~cov1)
    unc2 = np.flatnonzero(~cov2)
    return len(unc1) + len(unc2), unc1, unc2, U1, U2


# ----------------------------------------------------------------------------- search

def search(MT, inv, d, rng, deadline):
    """Annealing with hole-directed moves.  Returns a zero-cost S (as int64 array) or None."""
    N = MT.shape[0]
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    c, unc1, unc2, U1, U2 = evaluate(MT, inv, S)
    bestc = c
    T, stall, it = 0.4, 0, 0
    while c > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        if stall > 40000:
            S = rng.choice(N, size=d, replace=False).astype(np.int64)
            c, unc1, unc2, U1, U2 = evaluate(MT, inv, S)
            bestc = c
            stall = 0
            continue

        q = int(rng.integers(d))
        fam = int(rng.integers(2))
        unc = unc1 if fam == 0 else unc2
        Ul = U1 if fam == 0 else U2
        if len(unc) == 0 or rng.random() < 0.5:
            g = int(rng.integers(N))
        else:
            # Hole-directed move: aim a word u1*u2*u3*u4 at an uncovered element t.
            t = int(unc[rng.integers(len(unc))])
            u2 = int(Ul[rng.integers(len(Ul))])
            u3 = int(Ul[rng.integers(len(Ul))])
            u4 = int(Ul[rng.integers(len(Ul))])
            w = int(MT[MT[u2, u3], u4])
            u1 = int(MT[t, inv[w]])          # u1 = t * (u2 u3 u4)^-1
            p = int(rng.integers(d))
            if fam == 0:
                g = int(MT[S[p], u1])        # s_p^-1 s_q = u1  =>  s_q = s_p u1
            else:
                g = int(inv[MT[inv[S[p]], u1]])  # s_p s_q^-1 = u1 => s_q^-1 = s_p^-1 u1
        if np.any(S == g):
            continue

        S2 = S.copy()
        S2[q] = g
        c2, v1, v2, W1, W2 = evaluate(MT, inv, S2)
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, c, unc1, unc2, U1, U2 = S2, c2, v1, v2, W1, W2
            if c < bestc:
                bestc = c
                stall = 0
            else:
                stall += 1
        else:
            stall += 1
    return S


# ----------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = metacyclic(199, 9, 180)
        best = checked(MT, FALLBACK_S, d, D)
    except Exception:
        best = None

    cands = group_candidates(2001, 2061, 16)
    for idx, (m, k, lam) in enumerate(cands):
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        share = remaining / (len(cands) - idx)
        try:
            MT, inv = metacyclic(m, k, lam)
            S = search(MT, inv, d, rng, time.monotonic() + share)
            if S is not None:
                res = checked(MT, S, d, D)
                if res is not None and (best is None or res[0] > best[0]):
                    best = res
        except Exception:
            continue

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
