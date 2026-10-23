"""Haar-graph search with a product-move annealer for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a metacyclic group G = Z_m x|_r Z_k of order N and a connection set S of d elements.
The Haar graph has vertices A_g and B_g (g in G) and edges A_g ~ B_{s*g} for s in S. It is bipartite and
d-regular with 2N vertices. Its diameter is at most 5 when (S^-1 S)^2 = G and (S S^-1)^2 = G, so the
search minimises the number of uncovered group elements under these two conditions.

NEW HELPER (product move).  Besides uniform random replacement of one element of S, the annealer proposes
x = s_a * s_b for two elements of S. Such products tend to fill gaps in the word sets, and the move
is cheap. Groups are sampled from a window of orders just above the best order found so far, so each
success raises the target.

SAFETY.  Every candidate is verified with lib.is_valid before being accepted. A valid Haar graph
(2*1791 = 3582 vertices) from the parent is the fallback, so the output is never worse than the parent.
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
    """Z_m x|_r Z_k with element (a, j) -> a*k + j and (a, j)(b, l) = (a + r^j b, j + l). Returns (MT, inv)."""
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
    """All (m, k, r) with m*k = N giving a non-abelian metacyclic group Z_m x|_r Z_k."""
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


def make_cost(MT, inv, N):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2."""
    def cost(S):
        Si = inv[S]
        total = 0
        for T in (MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()):
            W = MT[T[:, None], T[None, :]].ravel()
            cov = np.zeros(N, dtype=bool)
            cov[W] = True
            total += N - int(np.count_nonzero(cov))
        return total
    return cost


def anneal(MT, inv, N, d, deadline, rng, max_stall=4000):
    """Anneal a connection set S. Returns S (cost 0) or None on stall or timeout."""
    cost = make_cost(MT, inv, N)
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    cur = cost(S)
    best = cur
    stall = 0
    while True:
        if cur == 0:
            return S
        if stall > max_stall or time.monotonic() > deadline:
            return None
        j = int(rng.integers(d))
        if rng.random() < 0.5:
            x = int(rng.integers(N))
        else:
            # Product move: x = s_a * s_b for two current elements.
            a = int(S[int(rng.integers(d))])
            b = int(S[int(rng.integers(d))])
            x = int(MT[a, b])
        if np.any(S == x):
            stall += 1
            continue
        old = int(S[j])
        S[j] = x
        c = cost(S)
        if c <= cur or rng.random() < math.exp(-(c - cur) / 0.6):
            cur = c
        else:
            S[j] = old
        if cur < best:
            best = cur
            stall = 0
        else:
            stall += 1


def haar_edges(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N + g, edges A_g ~ B_{s*g}."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        ys = N + MT[s].astype(np.int64)
        edges.extend(zip(ar.tolist(), ys.tolist()))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.75 * time_limit, time_limit - 10.0))
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

    lo = best_n // 2 + 1
    hi = lo + 250
    while time.monotonic() < deadline:
        N = int(rng.integers(lo, hi + 1))
        choices = metacyclic_choices(N)
        if not choices:
            continue
        m, k, r = choices[int(rng.integers(len(choices)))]
        try:
            MT, inv = group_table(m, k, r)
            S = anneal(MT, inv, N, d, deadline, rng)
        except Exception:
            continue
        if S is None:
            continue
        n, edges = haar_edges(MT, S, N)
        try:
            ok = n > best_n and lib.is_valid(n, edges, d, D)
        except Exception:
            ok = False
        if ok:
            best_n, best_edges = n, edges
        # Whether or not it improved, only look at larger orders afterwards.
        lo = max(lo, N + 1)
        hi = lo + 250

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
