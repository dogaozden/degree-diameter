"""Pure Haar-graph search for the d=10, D=5 target (a deliberately different construction).

CONSTRUCTION.  A Haar graph over a group G with connection set S (|S| = d) has vertices A_g and B_g for g in G,
and edges A_g ~ B_{s*g} for s in S.  It is bipartite, d-regular, and has 2|G| vertices.  Its diameter is at most 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  So the search minimises
    cost(S) = |G \\ (S^-1 S)^2| + |G \\ (S S^-1)^2|,
and a zero-cost S gives a valid graph.  Groups are non-abelian metacyclic Z_m x|_r Z_k, with orders chosen just
above half the best vertex count found so far.

SEARCH.  Simulated annealing over single-slot replacements in S, with a full cost recomputation per move.  Each
attempt uses a fresh random group and a random start, and runs for a fixed slice of time.  Every zero-cost result
is checked with lib.is_valid before it is accepted.

SAFETY.  The valid Haar graph from the parent (2*1791 = 3582 vertices) is verified first and used as the starting
best.  Any failure falls back to a valid small graph, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)

# Valid Haar fallback from the parent (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]

N_MAX = 2060          # largest group order tried (vertices = 2N)
ATTEMPT_SECONDS = 4.0 # time slice per (group, start) attempt


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j and (a, j)(b, l) = (a + r^j b, j + l).

    Returns (MT, inv): MT[x, y] is the index of x*y, and inv[x] is the index of x^-1.
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


def metacyclic_options(N):
    """All (m, k, r) with m*k = N, k >= 2, giving a NON-abelian group Z_m x|_r Z_k."""
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


# ------------------------------------------------------------------------------ cost

def make_cost(MT, inv, N):
    """Cost of a connection set S: group elements missed by (S^-1 S)^2 and by (S S^-1)^2."""

    def cost(S):
        Si = inv[S]
        mark = np.zeros(N, dtype=bool)
        mark[MT[Si[:, None], S[None, :]].ravel()] = True
        U = np.flatnonzero(mark)
        mark[:] = False
        mark[MT[U[:, None], U[None, :]].ravel()] = True
        c1 = N - int(np.count_nonzero(mark))

        mark[:] = False
        mark[MT[S[:, None], Si[None, :]].ravel()] = True
        U = np.flatnonzero(mark)
        mark[:] = False
        mark[MT[U[:, None], U[None, :]].ravel()] = True
        c2 = N - int(np.count_nonzero(mark))
        return c1 + c2

    return cost


def search(N, d, rng, t_end, cost):
    """Anneal a d-element set S to cost 0. Returns S (int64 array) or None if time runs out."""
    S = rng.choice(N, d, replace=False).astype(np.int64)
    cur = cost(S)
    step = 0
    L = 4000
    while cur > 0:
        if time.monotonic() >= t_end:
            return None
        step += 1
        T = 0.4 + 1.6 * (1.0 - (step % L) / L)
        i = int(rng.integers(d))
        g = int(rng.integers(N))
        if (S == g).any():
            continue
        old = S[i]
        S[i] = g
        c = cost(S)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            S[i] = old
    return S


# ------------------------------------------------------------------------------ edges

def haar_edges(MT, N, S):
    """Haar graph: A-vertex g is g, B-vertex x is N + x, and A_g ~ B_{s*g} for s in S."""
    A = np.arange(N, dtype=np.int64)
    src = []
    dst = []
    for s in sorted(set(int(x) for x in S)):
        src.append(A)
        dst.append(N + MT[s].astype(np.int64))
    src = np.concatenate(src)
    dst = np.concatenate(dst)
    return list(zip(src.tolist(), dst.tolist()))


# ------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.75 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        N = m * k
        e = haar_edges(MT, N, np.array(FALLBACK_S, dtype=np.int64))
        n = 2 * N
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        if lo > N_MAX:
            break
        try:
            N = int(rng.integers(lo, N_MAX + 1))
            opts = metacyclic_options(N)
            if not opts:
                continue
            m, k, r = opts[int(rng.integers(len(opts)))]
            MT, inv = group_table(m, k, r)
            cost = make_cost(MT, inv, N)
            t_end = min(deadline, time.monotonic() + ATTEMPT_SECONDS)
            S = search(N, d, rng, t_end, cost)
            if S is None:
                continue
            e = haar_edges(MT, N, S)
            n = 2 * N
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_edges = n, e
        except Exception:
            continue

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
