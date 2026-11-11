"""Haar-graph search with a proven diameter criterion and a table-based cost (d=10, D=5).

CONSTRUCTION.  For a finite group G and a set S of d elements, the Haar graph has vertices A_g and B_g (g in G),
and edges A_g ~ B_{s*g} for s in S. It is bipartite and d-regular on 2|G| vertices. Its diameter is at most 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. So the cost is (|G| - |(S^-1 S)^2|) + (|G| - |(S S^-1)^2|), and a graph is
valid exactly when the cost is 0.

NEW IN THIS VERSION.
  * The cost is evaluated directly from the group multiplication table with a few fancy-indexing operations
    (no BFS and no bitmasks), so the annealer does thousands of evaluations per second.
  * Left-normalisation: the cost is invariant under S -> g*S, so we fix the identity in S and search over d-1 slots.
  * Moves include random elements and products s_j*s_k of current members (cheap structured moves).
  * Groups are drawn at random from the metacyclic family Z_m x|_r Z_k with r != 1 (non-abelian), for orders N
    just above the best Haar order found so far.

Every zero-cost candidate is checked with lib.is_valid before it is accepted. A valid Haar graph (2*1791 = 3582
vertices, taken from an earlier search) is the fallback, so the output is never worse than that.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
STEPS = 2500


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j and (a, j)(b, l) = (a + r^j b, j + l).

    Returns (MT, inv) where MT[x, y] is the product x*y (int32) and inv[x] is the inverse of x.
    The identity has index 0.
    """
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
    """All non-abelian metacyclic presentations (m, k, r) with m*k = N, r != 1."""
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


def cost(MT, inv, S, N, mark):
    """Uncovered elements: (N - |(S^-1 S)^2|) + (N - |(S S^-1)^2|). Zero means diameter <= 5."""
    Sinv = inv[S]
    A = np.unique(MT[np.ix_(Sinv, S)])
    mark[:] = False
    mark[MT[np.ix_(A, A)]] = True
    c1 = int(np.count_nonzero(mark))
    C = np.unique(MT[np.ix_(S, Sinv)])
    mark[:] = False
    mark[MT[np.ix_(C, C)]] = True
    c2 = int(np.count_nonzero(mark))
    return 2 * N - c1 - c2


def anneal(MT, inv, N, d, rng, steps, deadline):
    """Simulated annealing over S (identity fixed in slot 0). Returns a zero-cost S or None."""
    mark = np.zeros(N, dtype=bool)
    S = np.empty(d, dtype=np.int64)
    S[0] = 0
    chosen = {0}
    i = 1
    while i < d:
        x = int(rng.integers(1, N))
        if x not in chosen:
            chosen.add(x)
            S[i] = x
            i += 1
    cur = cost(MT, inv, S, N, mark)
    for step in range(steps):
        if cur == 0:
            return S
        if (step & 127) == 0 and time.monotonic() >= deadline:
            return None
        pos = int(rng.integers(1, d))
        members = S.tolist()
        if rng.random() < 0.7:
            x = int(rng.integers(N))
        else:
            j = int(rng.integers(d))
            k = int(rng.integers(d))
            x = int(MT[S[j], S[k]])
        if x in members:
            continue
        old = int(S[pos])
        S[pos] = x
        c = cost(MT, inv, S, N, mark)
        temp = 0.2 + 2.0 * (1.0 - step / steps)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            S[pos] = old
    return S if cur == 0 else None


def haar_from(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N + g, and A_g ~ B_{s*g} for s in S."""
    ar = np.arange(N, dtype=np.int64)
    src = np.tile(ar, len(S))
    dst = N + MT[np.asarray(S, dtype=np.int64)].astype(np.int64).ravel()
    return 2 * N, list(zip(src.tolist(), dst.tolist()))


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
        n, e = haar_from(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    base = best_n // 2 if best_n else 1000
    while time.monotonic() < deadline:
        lo = base + 1
        N = lo + int(rng.integers(0, 24))
        choices = metacyclic_choices(N)
        if not choices:
            continue
        m, k, r = choices[int(rng.integers(len(choices)))]
        try:
            MT, inv = group_table(m, k, r)
            S = anneal(MT, inv, N, d, rng, STEPS, deadline)
        except Exception:
            continue
        if S is None:
            continue
        try:
            n, edges = haar_from(MT, S, N)
            ok = n > best_n and lib.is_valid(n, edges, d, D)
        except Exception:
            ok = False
        if ok:
            best_n, best_edges = n, edges
            base = best_n // 2

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
