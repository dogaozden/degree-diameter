"""Word-cover annealing for Haar graphs over metacyclic groups (bipartite degree-diameter, d=10, D=5).

NEW IDEA.  A Haar graph over a group G with connection set S (|S| = d) has 2|G| vertices and is d-regular
and bipartite. Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. The cost is the number of
uncovered group elements in those two word sets. Each cost evaluation is a few numpy gathers on a d x d
table, so the search runs far faster than the BFS-based cost of the parent.

Search moves mix uniform replacement with conjugation (s -> x s x^-1), which keeps many words intact.
Group order is targeted just above the record half (N in (best/2, best/2 + W]), since only |G| > 2000
beats the record of 4000 vertices. Only non-abelian metacyclic groups Z_m x|_r Z_k are used, because
abelian groups waste most words. Each group gets a time slice, and every zero-cost set is checked with
lib.is_valid before it is accepted. A valid Haar fallback of order 1791 is kept, so the output is never
worse than the parent.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
WINDOW = 60      # width of the group-order window above best/2
SLICE = 3.0      # seconds spent on one group before switching


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


def nonabelian_params(N):
    """All (m, k, r) with m*k = N, k >= 2, and r acting nontrivially (so the group is non-abelian)."""
    out = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and r % m != 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def haar_cost(MT, inv, N, S):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    iS = inv[S]
    L = MT[iS[:, None], S[None, :]].ravel()
    R = MT[S[:, None], iS[None, :]].ravel()
    c = 0
    for X in (L, R):
        sq = MT[X[:, None], X[None, :]].ravel()
        c += N - int(np.count_nonzero(np.bincount(sq, minlength=N)))
    return c


def anneal_group(MT, inv, N, d, rng, deadline):
    """Anneal connection sets in one group until cost 0 (returned) or the deadline (None)."""
    while time.monotonic() < deadline:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        cur = haar_cost(MT, inv, N, S)
        L = 4000
        for step in range(L):
            if cur == 0:
                return S
            if (step & 63) == 0 and time.monotonic() >= deadline:
                return None
            idx = int(rng.integers(d))
            if rng.random() < 0.5:
                new = int(rng.integers(N))
            else:
                x = int(rng.integers(N))
                new = int(MT[MT[x, S[idx]], inv[x]])
            if np.any(S == new):
                continue
            Sn = S.copy()
            Sn[idx] = new
            c = haar_cost(MT, inv, N, Sn)
            temp = max(0.05, 1.5 * (1.0 - step / L))
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                S, cur = Sn, c
    return None


def haar_from(MT, S, N):
    """Haar graph of the table group: A-vertex g is g, B-vertex g is N + g, edges (g, A) ~ (s*g, B)."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted({int(x) for x in S}):
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
        del MT
    except Exception:
        pass

    while time.monotonic() < deadline - 1.0:
        lo = best_n // 2 + 1
        N = int(rng.integers(lo, lo + WINDOW))
        params = nonabelian_params(N)
        if not params:
            continue
        m, k, r = params[int(rng.integers(len(params)))]
        try:
            MT, inv = group_table(m, k, r)
        except Exception:
            continue
        slice_end = min(deadline, time.monotonic() + SLICE)
        S = anneal_group(MT, inv, N, d, rng, slice_end)
        if S is not None:
            try:
                n, edges = haar_from(MT, S, N)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best_n, best_edges = n, edges
            except Exception:
                pass
        del MT, inv

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
