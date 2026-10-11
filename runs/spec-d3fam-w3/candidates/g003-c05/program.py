import math
import random
import time

import numpy as np

import lib


# ---------------------------------------------------------------- group-Haar search (D = 3)
#
# For a finite group G of order N and S a d-subset of G with 1 in S (WLOG), the bipartite
# Haar-type graph has a_g ~ b_{gs} for s in S. Left multiplication is an automorphism that
# is transitive on each side, so diameter <= 3 holds iff
#   (A)  S S^{-1} = G         (a-a pairs at distance 2)
#   (B)  S^{-1} S = G         (b-b pairs at distance 2)
#   (AB) S union S S^{-1} S = G  (a-b pairs at distance 1 or 3)
# Each such graph has 2N vertices, so N must satisfy N <= d^2 - d + 1.
# This explores non-abelian groups Z_m x|_r Z_k, which cyclic searches do not reach.

_TABLE_CACHE = {}


def _tables(m, k, r):
    """Multiplication and inverse tables of Z_m x|_r Z_k (cached)."""
    key = (m, k, r)
    if key not in _TABLE_CACHE:
        N, mul, inv = lib.semidirect_group(m, k, r)
        mt = np.array([[mul(x, y) for y in range(N)] for x in range(N)], dtype=np.int32)
        iv = np.array([inv(x) for x in range(N)], dtype=np.int32)
        _TABLE_CACHE[key] = (N, mt, iv)
    return _TABLE_CACHE[key]


def _groups_of_order(N, rng):
    """Candidate (m, k, r) with m*k = N: cyclic/direct products plus a few sampled twisted ones."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        out.append((m, k, 1))
        if k > 1:
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            for r in (rng.sample(rs, min(3, len(rs))) if rs else []):
                out.append((m, k, r))
    return out


def _cost(arr, N, mt, iv):
    """Number of uncovered elements over conditions (A), (B), (AB). Zero means valid."""
    invS = iv[arr]
    P = mt[np.ix_(arr, invS)].ravel()   # S S^{-1}
    Q = mt[np.ix_(invS, arr)].ravel()   # S^{-1} S
    R = mt[np.ix_(P, arr)].ravel()      # S S^{-1} S
    cA = np.zeros(N, dtype=bool)
    cA[P] = True
    cB = np.zeros(N, dtype=bool)
    cB[Q] = True
    cAB = np.zeros(N, dtype=bool)
    cAB[R] = True
    cAB[arr] = True
    return 3 * N - int(cA.sum()) - int(cB.sum()) - int(cAB.sum())


def _search(d, N, mt, iv, rng, deadline):
    """Annealing over S (size d, 1 in S) until cost 0 or the deadline. Returns S array or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    arr = np.array(S, dtype=np.int64)
    cost = _cost(arr, N, mt, iv)
    T = 0.5
    while cost > 0:
        if time.monotonic() >= deadline:
            return None
        idx = rng.randrange(1, d)
        new = rng.randrange(N)
        if new in S:
            continue
        arr2 = arr.copy()
        arr2[idx] = new
        c2 = _cost(arr2, N, mt, iv)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            arr = arr2
            S[idx] = new
            cost = c2
    return arr


def _graph_from(S, N, mt):
    """Bipartite graph: a_g = g, b_h = N + h, edges a_g ~ b_{g s} for s in S."""
    edges = []
    for g in range(N):
        for s in S:
            edges.append((g, N + int(mt[g, s])))
    return 2 * N, edges


def _group_phase(d, best_N, deadline, rng):
    """Sweep group orders N above best_N; round-robin over candidate groups with doubling slices."""
    mcap = d * d - d + 1
    entries = []
    for N in range(max(best_N + 1, d), mcap + 1):
        for m, k, r in _groups_of_order(N, rng):
            entries.append((N, m, k, r))
    if not entries:
        return None

    result = None
    best_found_N = best_N
    slice_t = max(0.2, (deadline - time.monotonic()) / (4 * len(entries)))
    while time.monotonic() < deadline:
        progressed = False
        for N, m, k, r in entries:
            if N <= best_found_N:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            progressed = True
            try:
                NN, mt, iv = _tables(m, k, r)
            except ValueError:
                continue
            S = _search(d, NN, mt, iv, rng, min(deadline, now + slice_t))
            if S is None:
                continue
            n, edges = _graph_from(S.tolist(), NN, mt)
            if lib.is_valid(n, edges, d, 3):
                result = (n, edges)
                best_found_N = NN
        if not progressed:
            break
        slice_t *= 2
    return result


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.8 * time_limit - 1.0)
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    kdd = lib.haar_graph(d, range(d))
    if not lib.is_valid(kdd[0], kdd[1], d, D):
        kdd = (1, [])
    best = kdd

    if D == 3:
        if d >= 3:
            # Structured base: projective plane or Araujo-Pardo-Lopez graph.
            base = None
            try:
                q = d - 1
                if q >= 2 and lib.is_prime_power(q):
                    base = lib.projective_plane_incidence(q)
                elif d - 2 >= 3 and lib.is_prime_power(d - 2):
                    base = lib.araujo_lopez_graph(d - 2)
            except Exception:
                base = None
            if base is not None and base[0] > best[0] and lib.is_valid(base[0], base[1], d, 3):
                best = base

            # Non-abelian group-Haar search for orders above the current best.
            if best[0] < lib.moore_bound(d, 3):
                res = _group_phase(d, best[0] // 2, deadline, rng)
                if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, 3):
                    best = res
    else:
        # Random Haar fallback for other diameters.
        m, misses = d + 1, 0
        while time.monotonic() < deadline and misses < 10:
            found = None
            for _ in range(30):
                if time.monotonic() >= deadline:
                    break
                S = [0] + rng.sample(range(1, m), d - 1)
                n, edges = lib.haar_graph(m, S)
                if lib.within_diameter(n, edges, D):
                    found = (n, edges)
                    break
            if found:
                if found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                    best = found
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return kdd
    return best
