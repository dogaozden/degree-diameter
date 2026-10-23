"""Haar-graph annealing for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  For a group G of order N and a connection set S of d elements, the Haar graph has
vertices A_g and B_g (g in G) and edges A_g ~ B_{s*g} for s in S.  It is bipartite, d-regular, and has
2N vertices.  Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  The target order needs N > 2000, so the search uses metacyclic non-abelian groups Z_m x|_r Z_k with
N in [2001, 2030].  For each random group, simulated annealing over S minimises the uncovered count
cost(S) = (N - |(S^-1 S)^2|) + (N - |(S S^-1)^2|).  Each step costs a few numpy operations on d^2-sized
sets.  A zero-cost S is turned into a graph and checked with lib.is_valid before it is accepted.  The
search then moves on to larger groups.

A valid Haar graph of order 3582 is the fallback, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
N_LO, N_HI = 2001, 2030


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


def metacyclic_candidates(N):
    """All non-abelian metacyclic Z_m x|_r Z_k of order N with m, k >= 2 and r != 1."""
    out = []
    for m in range(2, N // 2 + 1):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def cost(S, MT, inv, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    iS = inv[S]
    A = np.unique(MT[iS[:, None], S[None, :]])
    m1 = np.zeros(N, dtype=bool)
    m1[MT[A[:, None], A[None, :]]] = True
    B = np.unique(MT[S[:, None], iS[None, :]])
    m2 = np.zeros(N, dtype=bool)
    m2[MT[B[:, None], B[None, :]]] = True
    return 2 * N - int(m1.sum()) - int(m2.sum())


def anneal(MT, inv, N, d, rng, deadline, L=15000):
    """One annealing run from a random S.  Returns a zero-cost S, or None."""
    S = rng.choice(N, d, replace=False).astype(np.int64)
    cur = cost(S, MT, inv, N)
    for step in range(L):
        if cur == 0:
            return S
        if step % 2000 == 0 and time.monotonic() > deadline:
            return None
        i = int(rng.integers(d))
        g = int(rng.integers(N))
        if g in S:
            continue
        S2 = S.copy()
        S2[i] = g
        c = cost(S2, MT, inv, N)
        temp = 1.5 * (1.0 - step / L) + 0.1
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S, cur = S2, c
    return S if cur == 0 else None


def haar_from(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), vertices A = g, B = N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted({int(x) for x in S}):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_from(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    cands = {N: metacyclic_candidates(N) for N in range(N_LO, N_HI + 1)}

    while time.monotonic() < deadline:
        Ns = [N for N in cands if cands[N] and 2 * N > best_n]
        if not Ns:
            break
        N = Ns[int(rng.integers(len(Ns)))]
        m, k, r = cands[N][int(rng.integers(len(cands[N])))]
        try:
            MT, inv = group_table(m, k, r)
            S = anneal(MT, inv, N, d, rng, deadline)
            if S is None:
                continue
            n, e = haar_from(MT, S, N)
            ok = n > best_n and lib.is_valid(n, e, d, D)
        except Exception:
            ok = False
            e = None
        if ok:
            best_n, best_edges = n, e

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
