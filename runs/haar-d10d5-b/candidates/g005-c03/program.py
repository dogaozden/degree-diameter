"""Haar-graph search with a guided neighbour move for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a metacyclic group G = Z_m x|_r Z_k of order N with r != 1 (non-abelian) and a connection
set S of d distinct elements.  The Haar graph has vertices A_g = g and B_g = N + g, with edges A_g ~ B_{s*g}
for s in S.  It is bipartite, d-regular, and has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

NEW HELPER: guided neighbour move.  The uncovered elements of each covering condition are tracked.  To cover an
uncovered h, a slot is replaced by x = s_j * h^-1 (so x^-1 s_j = h) or x = h * s_j (so x s_j^-1 = h), with j
a different slot.  Otherwise a uniformly random element is used.  This is annealed with a Metropolis rule.

SEARCH.  Group orders are sampled just above the current best half-order, and each group gets a bounded run.
Any zero-cost S is checked with lib.is_valid before it is accepted.  The valid Haar fallback (3582 vertices)
is always kept, so the output is never worse than the parent's.
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
    """A random metacyclic group (m, k, r) of order N with r != 1 mod m, or None if there is none."""
    opts = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                opts.append((m, k, r))
    if not opts:
        return None
    return opts[int(rng.integers(len(opts)))]


def haar_cost(MT, inv, S, N):
    """Return (cost, uncovered1, uncovered2) for the two covering conditions of the Haar graph."""
    Si = inv[S]
    A = np.unique(MT[Si[:, None], S[None, :]])
    mark1 = np.zeros(N, dtype=bool)
    mark1[MT[A[:, None], A[None, :]].ravel()] = True
    unc1 = np.flatnonzero(~mark1)

    C = np.unique(MT[S[:, None], Si[None, :]])
    mark2 = np.zeros(N, dtype=bool)
    mark2[MT[C[:, None], C[None, :]].ravel()] = True
    unc2 = np.flatnonzero(~mark2)
    return int(unc1.size + unc2.size), unc1, unc2


def search(MT, inv, N, d, rng, deadline, steps):
    """Anneal a connection set S of size d; return a zero-cost S or None."""
    S = rng.choice(N, d, replace=False).astype(np.int64)
    cur, u1, u2 = haar_cost(MT, inv, S, N)
    for step in range(steps):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            return None
        i = int(rng.integers(d))
        j = (i + 1 + int(rng.integers(d - 1))) % d
        if (u1.size + u2.size) > 0 and rng.random() < 0.6:
            # Guided move: make some uncovered element a single word of the set.
            if u1.size and (u2.size == 0 or rng.random() < 0.5):
                h = int(u1[int(rng.integers(u1.size))])
                x = int(MT[S[j], inv[h]])          # x^-1 s_j = h
            else:
                h = int(u2[int(rng.integers(u2.size))])
                x = int(MT[h, S[j]])               # x s_j^-1 = h
        else:
            x = int(rng.integers(N))
        if np.any(S == x):
            continue
        S2 = S.copy()
        S2[i] = x
        c2, v1, v2 = haar_cost(MT, inv, S2, N)
        temp = 0.05 + 1.0 * (1.0 - step / steps)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            S, cur, u1, u2 = S2, c2, v1, v2
    return S if cur == 0 else None


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
    budget = max(2.0, min(0.85 * time_limit, time_limit - 6.0))
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
        lo = max(best_n // 2 + 1, 1800)
        hi = lo + 120
        N = int(rng.integers(lo, hi + 1))
        G = random_nonabelian(N, rng)
        if G is None:
            continue
        m, k, r = G
        try:
            MT, inv = group_table(m, k, r)
            S = search(MT, inv, N, d, rng, deadline, steps=6000)
            if S is None:
                continue
            n, e = haar_from(MT, S, N)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_edges = n, e
        except Exception:
            continue

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
