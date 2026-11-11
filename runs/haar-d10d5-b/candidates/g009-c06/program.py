"""Non-abelian Haar-graph search for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a metacyclic group G = Z_m x|_r Z_k of order N (N in [2001, 2300], so 2N exceeds the
record 4000) and a connection set S of d distinct group elements.  The Haar graph has vertices A_g and B_g
for g in G, and edges A_g ~ B_{s*g} for s in S.  It is bipartite, d-regular, and has 2N vertices.

CRITERION.  The diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  So
cost(S) = (N - |(S^-1 S)^2|) + (N - |(S S^-1)^2|) is zero exactly for valid connection sets.

SEARCH.  Simulated annealing over S: one slot is replaced by a random element per step, with Metropolis
acceptance.  Restarts happen when a run stalls, and each restart draws a fresh group.  Any zero-cost S is
built and checked with lib.is_valid before it is accepted.

SAFETY.  The valid Haar graph of order 3582 from the parent is checked first and kept as the fallback, so the
output is never worse than it.  Other (d, D) cases use small valid constructions.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
N_LO, N_HI = 2001, 2300
STALL = 4000


def trivial(d, D):
    """Small always-valid graph for other (d, D), with a last-resort fallback."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e
    try:
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return 2, [(0, 1)]


def group_table(m, k, r):
    """Z_m x|_r Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (MT, inv)."""
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


def group_options(N):
    """All (m, k, r) giving a non-abelian metacyclic group Z_m x|_r Z_k of order N."""
    opts = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def cost(S, MT, inv, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    Si = inv[S]
    A = np.unique(MT[Si[:, None], S[None, :]])
    B = MT[A[:, None], A[None, :]].ravel()
    c1 = int(np.count_nonzero(np.bincount(B, minlength=N)))
    C = np.unique(MT[S[:, None], Si[None, :]])
    E = MT[C[:, None], C[None, :]].ravel()
    c2 = int(np.count_nonzero(np.bincount(E, minlength=N)))
    return 2 * N - c1 - c2


def haar_edges(MT, S, N):
    """Edges A_g ~ B_{s g} with A_g = g and B_g = N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
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

    Ns = list(range(N_LO, N_HI + 1))
    while time.monotonic() < deadline:
        N = int(Ns[int(rng.integers(len(Ns)))])
        opts = group_options(N)
        if not opts:
            continue
        m, k, r = opts[int(rng.integers(len(opts)))]
        try:
            MT, inv = group_table(m, k, r)
        except Exception:
            continue

        S = rng.choice(N, d, replace=False).astype(np.int64)
        cur = cost(S, MT, inv, N)
        run_best = cur
        stale = 0
        found = False
        while cur > 0 and stale < STALL and time.monotonic() < deadline:
            i = int(rng.integers(d))
            x = int(rng.integers(N))
            if np.any(S == x):
                stale += 1
                continue
            old = int(S[i])
            S[i] = x
            c = cost(S, MT, inv, N)
            temp = 0.8
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                S[i] = old
            if cur < run_best:
                run_best = cur
                stale = 0
            else:
                stale += 1
            if cur == 0:
                found = True

        if found:
            try:
                n, e = haar_edges(MT, S, N)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_edges = n, e
            except Exception:
                pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
