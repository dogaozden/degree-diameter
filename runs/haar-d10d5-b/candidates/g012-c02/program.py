"""Single-orbit Haar search for the bipartite degree-diameter problem (d=10, D=5), with two new ideas.

IDEA 1: Vectorised two-sided coverage cost.  For a Haar graph over a group G with connection set S, the
diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  The cost is the number of uncovered
elements of G on both sides.  It is computed with numpy gathers on the multiplication table, one full
evaluation per move (about 10^4 table lookups).

IDEA 2: Mixed proposal moves.  A slot of S is replaced by (a) a uniform random element, (b) a product of
two current elements, or (c) a conjugate c*s*c^-1 of a current element.  Moves (b) and (c) keep the
search inside structured regions of the group, where covering words are more likely to overlap usefully.

SEARCH.  The group order N is swept upward from the best known Haar graph.  For each N we draw a random
non-abelian metacyclic group Z_m x| Z_k and run annealing with restarts, under a per-group time slice.
Any zero-cost S is turned into a graph and checked with lib.is_valid before it is accepted.  The valid
Haar graph from the parent (3582 vertices) is the fallback, so the output is never worse than the parent.
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
    """Z_m x|_r Z_k with element (a, j) -> a*k + j.  Returns (MT, inv) with MT[x, y] = x*y."""
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
    """A random non-abelian metacyclic group of order N when one exists, otherwise cyclic."""
    cands = []
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    if not cands:
        return group_table(1, N, 1)
    m, k, r = cands[int(rng.integers(len(cands)))]
    return group_table(m, k, r)


def make_cost(MT, inv, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2 in G (0 iff the Haar graph has diameter <= 5)."""
    def cost(S):
        iS = inv[S]
        A = MT[iS[:, None], S[None, :]].ravel()
        B = MT[S[:, None], iS[None, :]].ravel()
        mark = np.zeros(N, dtype=bool)
        mark[MT[A[:, None], A[None, :]].ravel()] = True
        c = N - int(mark.sum())
        mark[:] = False
        mark[MT[B[:, None], B[None, :]].ravel()] = True
        return c + N - int(mark.sum())
    return cost


def haar_edges(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, and g joins N + s*g for each s in S."""
    ar = np.arange(N, dtype=np.int64)
    out = []
    for s in S:
        col = N + MT[int(s)].astype(np.int64)
        out.extend(zip(ar.tolist(), col.tolist()))
    return 2 * N, out


def search_group(N, d, D, rng, deadline):
    """Anneal S in a random group of order N until a valid Haar graph is found or the deadline passes."""
    MT, inv = random_group(N, rng)
    cost = make_cost(MT, inv, N)
    L = 15000
    while time.monotonic() < deadline:
        S = rng.choice(N, size=d, replace=False).astype(np.int64)
        cur = cost(S)
        for step in range(L):
            if (step & 255) == 0 and time.monotonic() >= deadline:
                return None
            u = rng.random()
            i = int(rng.integers(d))
            if u < 0.4:
                g = int(rng.integers(N))
            elif u < 0.7:
                a, b = rng.integers(d, size=2)
                g = int(MT[S[a], S[b]])
            else:
                j = int(rng.integers(d))
                c = int(rng.integers(N))
                g = int(MT[MT[c, S[j]], inv[c]])
            if np.any(S == g):
                continue
            old = int(S[i])
            S[i] = g
            c_new = cost(S)
            temp = 3.0 * (1.0 - step / L) + 0.5
            if c_new <= cur or rng.random() < math.exp(-(c_new - cur) / temp):
                cur = c_new
                if cur == 0:
                    n, edges = haar_edges(MT, S, N)
                    if lib.is_valid(n, edges, d, D):
                        return n, edges
                    return None
            else:
                S[i] = old
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + max(2.0, min(0.80 * time_limit, time_limit - 8.0))
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

    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        N = lo + int(rng.integers(0, 30))
        slice_end = min(deadline, time.monotonic() + 8.0)
        try:
            res = search_group(N, d, D, rng, slice_end)
        except Exception:
            res = None
        if res is not None:
            n, e = res
            if n > best_n:
                best_n, best_edges = n, e

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
