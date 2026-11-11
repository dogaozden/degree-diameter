"""Haar-graph search for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a finite group G of order N and a connection set S of d elements.  The Haar graph has
vertices A_g and B_g (g in G) and edges A_g ~ B_(s*g) for s in S.  It is bipartite, d-regular, has 2N
vertices, and every A-vertex looks the same.  Its diameter is at most 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  Left-translating S by a fixed element changes neither set, so 1 is
always in S and only d-1 elements are searched.

SEARCH.  For each candidate non-abelian metacyclic group Z_m x|_r Z_k with order N just above 1791, run
simulated annealing on S.  The cost is the number of group elements missing from the two squared sets,
which is evaluated with numpy on the multiplication table.  Each step proposes a few single-element
replacements and keeps the best one under a Metropolis rule.  Restarts happen when a run stalls.  Any
zero-cost S is turned into a graph and checked with lib.is_valid before it is accepted.  The fallback is the
parent's valid Haar graph on 3582 vertices, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
K_PROPOSALS = 6
STEPS_PER_RESTART = 3000
SLICE_SECONDS = 3.0

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


def candidate_groups(lo, hi, rng):
    """Non-abelian metacyclic groups (m, k, r) with order N in [lo, hi], sorted by N, shuffled within each N."""
    out = []
    for N in range(lo, hi + 1):
        cur = []
        for m in range(2, N):
            if N % m:
                continue
            k = N // m
            if k < 2:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    cur.append((m, k, r))
        rng.shuffle(cur)
        out.extend(cur)
    return out


def missing(MT, T, N):
    """Number of group elements not in the square {x*y : x, y in T}."""
    U = np.unique(T)
    P = MT[U[:, None], U[None, :]]
    mark = np.zeros(N, dtype=bool)
    mark[P.ravel()] = True
    return N - int(mark.sum())


def cost(MT, inv, S, N):
    """Uncovered elements in (S^-1 S)^2 plus uncovered elements in (S S^-1)^2.  Zero iff diameter <= 5."""
    iS = inv[S]
    T1 = MT[iS[:, None], S[None, :]].ravel()  # s^-1 t
    T2 = MT[S[:, None], iS[None, :]].ravel()  # s t^-1
    return missing(MT, T1, N) + missing(MT, T2, N)


def search(MT, inv, N, d, rng, t_stop):
    """Anneal S (with 0 = identity fixed in S) until cost 0 or t_stop.  Returns S or None."""
    while time.monotonic() < t_stop:
        S = np.concatenate(([0], rng.choice(np.arange(1, N), d - 1, replace=False))).astype(np.int64)
        cur = cost(MT, inv, S, N)
        for step in range(STEPS_PER_RESTART):
            if cur == 0:
                return S
            if (step & 63) == 0 and time.monotonic() >= t_stop:
                return None
            temp = 3.0 * (0.1 ** (step / STEPS_PER_RESTART))
            pos = int(rng.integers(1, d))
            best, bestc = None, None
            for _ in range(K_PROPOSALS):
                x = int(rng.integers(1, N))
                if np.any(S == x):
                    continue
                S2 = S.copy()
                S2[pos] = x
                c = cost(MT, inv, S2, N)
                if bestc is None or c < bestc:
                    best, bestc = S2, c
            if best is None:
                continue
            if bestc <= cur or rng.random() < math.exp(-(bestc - cur) / temp):
                S, cur = best, bestc
        if cur == 0:
            return S
    return None


def haar_from(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), vertices A = g, B = N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 6.0))
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

    groups = candidate_groups(1792, 2060, rng)
    if not groups:
        groups = [FALLBACK_GROUP]
    gi = 0
    while time.monotonic() < deadline and groups:
        m, k, r = groups[gi % len(groups)]
        gi += 1
        N = m * k
        if 2 * N <= best_n:
            continue
        slice_end = min(deadline, time.monotonic() + SLICE_SECONDS)
        try:
            MT, inv = group_table(m, k, r)
            S = search(MT, inv, N, d, rng, slice_end)
            if S is not None:
                n, e = haar_from(MT, S, N)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_edges = n, e
        except Exception:
            pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
