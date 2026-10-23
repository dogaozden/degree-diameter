"""Haar-graph word-cover search for the bipartite degree-diameter problem (d=10, D=5).

NEW IDEA (this version): a direct word-cover cost with identity normalisation.
For a Haar graph on group G with connection set S (|S| = d), diameter <= 5 holds iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  The cost is the number of uncovered elements of
G under those two conditions.  Each evaluation is a few numpy gathers on a precomputed
multiplication table (d^2 x d^2 products per condition), so about 1e4 candidate sets
can be scored per second.

Two extra moves beyond the parent:
  * Left translation of S is an isomorphism, so WLOG the identity lies in S.  Only the
    other d-1 slots are searched.
  * Best-of-K replacement: at each step, K random single-slot replacements are scored and
    the best one is accepted by a Metropolis rule.  Stagnating runs restart on a fresh
    random metacyclic group whose order is chosen just above the current record half.

Every zero-cost set is turned into a Haar graph and checked with lib.is_valid before it
is accepted.  The valid 3582-vertex Haar graph from the parent is kept as the fallback.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
SLICE_SECONDS = 4.0
K_MOVES = 6
TEMP = 0.6
STAGNATION_LIMIT = 3000


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


def metacyclic_candidates(N):
    """All (m, k, r) with m*k = N giving a non-abelian metacyclic group Z_m x|_r Z_k."""
    out = []
    for m in range(2, N // 2 + 1):
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

def word_cost(MT, inv, N, S):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2.  Zero iff diameter <= 5."""
    Si = inv[S]
    P = MT[Si[:, None], S[None, :]].ravel()          # s^-1 t
    mark = np.zeros(N, dtype=bool)
    mark[MT[P[:, None], P[None, :]].ravel()] = True
    c = N - int(np.count_nonzero(mark))
    Q = MT[S[:, None], Si[None, :]].ravel()          # s t^-1
    mark[:] = False
    mark[MT[Q[:, None], Q[None, :]].ravel()] = True
    c += N - int(np.count_nonzero(mark))
    return c


# ------------------------------------------------------------------------------ search

def anneal(MT, inv, N, d, rng, t_end):
    """Best-of-K Metropolis search over connection sets containing the identity.

    Returns a zero-cost S (int64 array), or None if time runs out or the run stagnates.
    """
    S = np.empty(d, dtype=np.int64)
    S[0] = 0
    S[1:] = rng.choice(np.arange(1, N), size=d - 1, replace=False)
    cur = word_cost(MT, inv, N, S)
    best_seen = cur
    last_improve = 0
    step = 0
    while time.monotonic() < t_end:
        if cur == 0:
            return S
        best_c, best_S = None, None
        for _ in range(K_MOVES):
            i = 1 + int(rng.integers(d - 1))
            g = int(rng.integers(N))
            if np.any(S == g):
                continue
            S2 = S.copy()
            S2[i] = g
            c = word_cost(MT, inv, N, S2)
            if best_c is None or c < best_c:
                best_c, best_S = c, S2
        step += 1
        if best_S is not None:
            if best_c <= cur or rng.random() < math.exp(-(best_c - cur) / TEMP):
                S, cur = best_S, best_c
                if cur < best_seen:
                    best_seen = cur
                    last_improve = step
        if step - last_improve > STAGNATION_LIMIT:
            return None
    if cur == 0:
        return S
    return None


def haar_edges(MT, S, N):
    """Haar graph of the table group: A-vertex g is g, B-vertex g is N + g; edge (g, N + s*g) for s in S."""
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
    budget = max(2.0, min(0.75 * time_limit, time_limit - 10.0))
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

    while time.monotonic() < deadline - 1.0:
        target_N = best_n // 2 + 1
        N = target_N + int(rng.integers(0, 40))
        cands = metacyclic_candidates(N)
        if not cands:
            continue
        m, k, r = cands[int(rng.integers(len(cands)))]
        try:
            MT, inv = group_table(m, k, r)
        except Exception:
            continue
        slice_end = min(deadline, time.monotonic() + SLICE_SECONDS)
        S = anneal(MT, inv, N, d, rng, slice_end)
        if S is None:
            continue
        try:
            n, e = haar_edges(MT, S, N)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_edges = n, e
        except Exception:
            pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
