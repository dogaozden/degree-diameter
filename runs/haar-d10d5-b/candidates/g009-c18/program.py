"""Haar-graph annealing for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a non-abelian metacyclic group G = Z_m x|_r Z_k of order N and a connection set S of d
elements.  The Haar graph has vertices (g, A) and (g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.
It is bipartite, d-regular, and has 2N vertices.  Its diameter is at most 5 iff (S^-1 S)^2 = G and
(S S^-1)^2 = G, so cost(S) counts the uncovered elements of those two sets and the graph is valid when the
cost is 0.

SEARCH.  For each order N slightly above the current best half-order, pick a random non-abelian metacyclic group
of that order.  Run simulated annealing on S (single-slot replacement moves, Metropolis acceptance, restarts)
until the cost reaches 0 or the per-group budget runs out.  Every zero-cost graph is checked with lib.is_valid
before it is accepted.  The validated Haar fallback from the parent (3582 vertices) is kept as the floor, so the
output is never worse than before.
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

GROUP_BUDGET = 4.0   # seconds spent annealing on one group before moving on
STEPS = 4000         # annealing steps per restart
OFFSET = 40          # new orders tried in [best_half + 1, best_half + OFFSET]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

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


def metacyclic_choices(N):
    """All (m, k, r) with m*k = N, k >= 2, and r != 1 giving a non-abelian Z_m x|_r Z_k."""
    out = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


# ------------------------------------------------------------------------------ Haar search

def haar_cost(MT, inv, N, S):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2 in G; zero iff the Haar graph has diameter <= 5."""
    Sa = np.asarray(S, dtype=np.int64)
    Si = inv[Sa]
    total = 0
    for X, Y in ((Si, Sa), (Sa, Si)):
        T = np.unique(MT[X[:, None], Y[None, :]])
        P = MT[T[:, None], T[None, :]].ravel()
        mark = np.zeros(N, dtype=bool)
        mark[P] = True
        total += N - int(mark.sum())
    return total


def haar_anneal(MT, inv, N, d, rng, t_end, steps):
    """Anneal S until cost 0 (return S as a list of ints) or time/steps run out (return None)."""
    S = [int(x) for x in rng.choice(N, d, replace=False)]
    cur = haar_cost(MT, inv, N, S)
    for step in range(steps):
        if cur == 0:
            return S
        if time.monotonic() > t_end:
            break
        i = int(rng.integers(d))
        g = int(rng.integers(N))
        if g in S:
            continue
        new = S.copy()
        new[i] = g
        c = haar_cost(MT, inv, N, new)
        temp = 1.0 * (1.0 - step / steps) + 0.15
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S, cur = new, c
    return S if cur == 0 else None


def haar_from(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), vertices A = g, B = N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


# ------------------------------------------------------------------------------ build

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

    while time.monotonic() < deadline:
        N_lo = best_n // 2 + 1
        N = N_lo + int(rng.integers(OFFSET))
        choices = metacyclic_choices(N)
        if not choices:
            continue
        m, k, r = choices[int(rng.integers(len(choices)))]
        try:
            MT, inv = group_table(m, k, r)
        except Exception:
            continue
        group_end = min(deadline, time.monotonic() + GROUP_BUDGET)
        found = None
        while time.monotonic() < group_end and found is None:
            found = haar_anneal(MT, inv, N, d, rng, group_end, STEPS)
        if found is not None:
            try:
                n, e = haar_from(MT, found, N)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_edges = n, e
            except Exception:
                pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
