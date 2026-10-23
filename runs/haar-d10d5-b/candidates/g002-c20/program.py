"""Haar-graph search for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a finite group G of order N and a set S of d elements.  The Haar graph H(G,S) has vertices
(g,A) and (g,B) for g in G, with (g,A) ~ (s*g,B) for s in S.  It is bipartite, d-regular, and has 2N vertices.

CRITERION.  Its diameter is at most 5 iff X = (S^-1 S)^2 covers G and Y = (S S^-1)^2 covers G.  So the search
anneals S directly on the cost (uncovered elements of X) + (uncovered elements of Y).  Each cost is two small
table-lookup products on the group multiplication table, so one evaluation is much cheaper than a full BFS.

SEARCH.  Non-abelian metacyclic groups Z_m x|_r Z_k with N just above the current best group order (best_n / 2).
Each attempt draws N from a small window above that threshold, anneals S with restarts, and checks any zero-cost
result with lib.is_valid before accepting it.  The verified Haar graph on 1791 elements (3582 vertices) is the
fallback, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
D_DEG = 10

# Valid Haar fallback from the parent (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]

WINDOW = 40        # group orders tried above the current threshold
STEPS = 3000       # annealing steps per start
RESTARTS = 4       # random starts per group


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


def random_nonabelian(N, rng):
    """A random non-abelian metacyclic group of order N as (MT, inv), or None if none exists."""
    cands = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if r != 1 and math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    if not cands:
        return None
    m, k, r = cands[int(rng.integers(len(cands)))]
    return group_table(m, k, r)


# ------------------------------------------------------------------------------ search

def cost(MT, inv, S, N, mark):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2; zero iff diameter <= 5."""
    Si = inv[S]
    A = np.unique(MT[Si[:, None], S[None, :]])
    mark[:] = False
    mark[MT[A[:, None], A[None, :]]] = True
    c1 = N - int(np.count_nonzero(mark))
    B = np.unique(MT[S[:, None], Si[None, :]])
    mark[:] = False
    mark[MT[B[:, None], B[None, :]]] = True
    c2 = N - int(np.count_nonzero(mark))
    return c1 + c2


def anneal(MT, inv, N, d, rng, mark, steps, deadline):
    """Simulated annealing on S; returns (S, cost).  Stops early at cost 0 or at the deadline."""
    S = rng.choice(N, d, replace=False).astype(np.int64)
    cur = cost(MT, inv, S, N, mark)
    for step in range(steps):
        if cur == 0:
            break
        if (step & 63) == 0 and time.monotonic() > deadline:
            break
        temp = 1.5 * (1.0 - step / steps) + 0.15
        pos = int(rng.integers(d))
        g = int(rng.integers(N))
        if np.any(S == g):
            continue
        S2 = S.copy()
        S2[pos] = g
        c = cost(MT, inv, S2, N, mark)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S, cur = S2, c
    return S, cur


def haar_from(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), vertices A = g, B = N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted({int(x) for x in S}):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


# ------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.78 * time_limit, time_limit - 8.0))
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

    lo = best_n // 2 + 1  # a Haar graph beats the best only if its group order exceeds best_n / 2
    while time.monotonic() < deadline:
        N = lo + int(rng.integers(WINDOW))
        try:
            grp = random_nonabelian(N, rng)
        except Exception:
            grp = None
        if grp is None:
            continue
        MT, inv = grp
        mark = np.zeros(N, dtype=bool)
        found = None
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                break
            S, c = anneal(MT, inv, N, d, rng, mark, STEPS, deadline)
            if c == 0:
                found = S
                break
        if found is not None:
            try:
                n, e = haar_from(MT, found, N)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_edges = n, e
                    lo = best_n // 2 + 1
            except Exception:
                pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
