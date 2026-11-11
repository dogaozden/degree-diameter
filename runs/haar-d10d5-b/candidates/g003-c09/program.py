"""Haar-graph annealing over metacyclic groups for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  For a group G of order N and a set S of d elements, the Haar graph on (g, A), (g, B) with
edges (g, A) ~ (s*g, B) is bipartite and d-regular on 2N vertices. Its diameter is at most 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.

NEW HELPER.  haar_cost counts the uncovered group elements of both words with one fancy-indexed table
lookup per word (d^2 products, then d^4 products of those) and a bincount, so each move costs a few
tens of microseconds.

SEARCH.  For each candidate order N just above the current best half-order, draw a random metacyclic
group table and run simulated annealing on S, replacing one element per move, with random restarts when
stuck. Any zero-cost S is checked with lib.is_valid before it is accepted. A valid Haar graph on
2*1791 = 3582 vertices is the fallback, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l). Returns (MT, inv)."""
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


def random_group(N, rng):
    """A random metacyclic group of order N, non-abelian when possible."""
    cands = [(m, N // m) for m in range(2, N) if N % m == 0 and N // m >= 2]
    if not cands:
        return group_table(1, N, 1)  # cyclic
    m, k = cands[int(rng.integers(len(cands)))]
    rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    r = rs[int(rng.integers(len(rs)))] if rs else 1
    return group_table(m, k, r)


def haar_cost(MT, inv, S, N):
    """Number of group elements missed by (S^-1 S)^2 plus those missed by (S S^-1)^2. Zero iff diameter <= 5."""
    Si = inv[S]
    cost = 0
    for X, Y in ((Si, S), (S, Si)):
        P = MT[X[:, None], Y[None, :]].ravel().astype(np.int64)
        Q = MT[P[:, None], P[None, :]].ravel()
        cost += N - int(np.count_nonzero(np.bincount(Q, minlength=N)))
    return cost


def anneal_haar(MT, inv, N, d, rng, max_seconds):
    """Anneal a connection set S for up to max_seconds. Returns a zero-cost S or None."""
    stop = time.monotonic() + max_seconds
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    cur = haar_cost(MT, inv, S, N)
    temp = 1.5
    since = 0
    while time.monotonic() < stop:
        if cur == 0:
            return S
        i = int(rng.integers(d))
        g = int(rng.integers(N))
        if g in S:
            continue
        T2 = S.copy()
        T2[i] = g
        c = haar_cost(MT, inv, T2, N)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            if c < cur:
                since = 0
            S, cur = T2, c
        since += 1
        temp = max(0.08, temp * 0.9997)
        if since > 4000:  # restart from a fresh random set
            S = rng.choice(N, size=d, replace=False).astype(np.int64)
            cur = haar_cost(MT, inv, S, N)
            temp = 1.5
            since = 0
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

    best_N = best_n // 2
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        N = int(rng.integers(best_N + 1, best_N + 150))
        try:
            MT, inv = random_group(N, rng)
        except Exception:
            continue
        S = anneal_haar(MT, inv, N, d, rng, min(5.0, remaining))
        if S is None:
            continue
        try:
            n, e = haar_from(MT, S, N)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_edges = n, e
                best_N = N
        except Exception:
            pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
