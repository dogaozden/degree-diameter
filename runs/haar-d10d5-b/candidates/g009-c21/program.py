"""Haar-graph search with an uncovered-directed move for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  A Haar graph over a finite group G with connection set S (|S| = d) has vertices A_g, B_g
(g in G) and edges A_g ~ B_{s*g} for s in S.  It is bipartite, d-regular, and has 2|G| vertices.  Its
diameter is at most 5 when (S^-1 S)^2 = G and (S S^-1)^2 = G.  The cost is the number of uncovered
elements on the two sides.

NEW IDEA (uncovered-directed move).  A uniformly random replacement of one element of S almost always
breaks coverage that already exists.  Instead, pick an uncovered element u of one side, pick a random
element c of the current word set X = S^-1 S (or Y = S S^-1), and set y = c^-1 u.  Then choose the new
slot value so that the new word s'^-1 a (or s' a^-1) equals y, which makes u = c * y covered.  The
proposal is then accepted by the usual Metropolis rule on the true cost, so the move is only a
heuristic.  It is mixed with uniform random moves.

SEARCH.  Metacyclic groups Z_m x|_r Z_k are sampled with orders just above the threshold (record/2 is
2000, the fallback is 1791).  Each group gets an annealing run with a restart on each new random S.
Any zero-cost configuration is verified with lib.is_valid.  The fixed Haar fallback (3582 vertices) is
kept as the baseline, so the output is never worse.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10

# Valid Haar fallback from the parent (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (MT, inv)."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 128
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def metacyclic_options(N):
    """All non-abelian metacyclic Z_m x|_r Z_k of order N as (m, k, r) triples."""
    out = []
    for m in range(2, N):
        if N % m or N // m < 2:
            continue
        k = N // m
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def evaluate(S, MT, inv, N):
    """Cost of S: uncovered elements of (S^-1 S)^2 and (S S^-1)^2, plus the covers and word sets."""
    Si = inv[S]
    X = np.unique(MT[Si[:, None], S[None, :]])     # s^-1 t
    P1 = np.unique(MT[X[:, None], X[None, :]])     # (S^-1 S)^2
    Y = np.unique(MT[S[:, None], Si[None, :]])     # s t^-1
    P2 = np.unique(MT[Y[:, None], Y[None, :]])     # (S S^-1)^2
    return 2 * N - len(P1) - len(P2), P1, P2, X, Y


def anneal(N, MT, inv, d, rng, deadline, L=4000):
    """Annealing over connection sets; returns a zero-cost S (int64 array) or None at the deadline."""
    while time.monotonic() < deadline:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        c, P1, P2, X, Y = evaluate(S, MT, inv, N)
        for step in range(L):
            if c == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            T = 2.0 * (1.0 - step / L) + 0.15
            i = int(rng.integers(d))
            if rng.random() < 0.5:
                new = int(rng.integers(N))
            else:
                # Uncovered-directed move: make a chosen uncovered element u equal c * y.
                side = int(rng.integers(2))
                cov = P1 if side == 0 else P2
                pool = X if side == 0 else Y
                covered = np.zeros(N, dtype=bool)
                covered[cov] = True
                unc = np.flatnonzero(~covered)
                if len(unc) == 0:
                    new = int(rng.integers(N))
                else:
                    u = int(unc[int(rng.integers(len(unc)))])
                    ce = int(pool[int(rng.integers(len(pool)))])
                    y = int(MT[inv[ce], u])            # y = ce^-1 * u
                    j = (i + 1 + int(rng.integers(d - 1))) % d
                    a = int(S[j])
                    if side == 0:
                        new = int(MT[a, inv[y]])       # s'^-1 a = y
                    else:
                        new = int(MT[y, a])            # s' a^-1 = y
            if np.any(S == new):
                continue
            S2 = S.copy()
            S2[i] = new
            c2, P1b, P2b, Xb, Yb = evaluate(S2, MT, inv, N)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                S, c, P1, P2, X, Y = S2, c2, P1b, P2b, Xb, Yb
    return None


def haar_edges(MT, S, N):
    """Haar graph: vertices A_g = g and B_g = N + g, with edges A_g ~ B_{s*g} for s in S."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        targets = N + MT[s].astype(np.int64)
        edges.extend(zip(ar.tolist(), targets.tolist()))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_edges(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        N = lo + int(rng.integers(0, 40))
        try:
            opts = metacyclic_options(N)
            if opts:
                m, k, r = opts[int(rng.integers(len(opts)))]
                MT, inv = group_table(m, k, r)
            else:
                MT, inv = group_table(1, N, 1)
            slice_end = min(deadline, time.monotonic() + 6.0)
            S = anneal(N, MT, inv, d, rng, slice_end)
            if S is not None:
                n, edges = haar_edges(MT, S, N)
                ok = n > best_n and lib.is_valid(n, edges, d, D)
                if ok:
                    best_n, best_edges = n, edges
        except Exception:
            continue

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
