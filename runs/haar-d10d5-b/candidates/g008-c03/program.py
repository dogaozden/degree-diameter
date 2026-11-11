"""Fast Haar-graph annealing for the bipartite degree-diameter problem (d=10, D=5).

NEW IDEA: exact incremental cover-cost for Haar graphs.
For the Haar graph of a group G with connection set S (|S| = d), the diameter is at most 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. The routine `cover_cost` computes the number of uncovered
elements of both squares with a few numpy gathers (about 100 products, then up to ~8000 products
in a boolean mark array), so one candidate costs roughly 0.1-0.2 ms. The annealer uses it as a
fitness function: at each step it tries K random single-slot replacements, keeps the best one, and
applies a Metropolis acceptance rule. Groups are non-abelian metacyclic Z_m x| Z_k of order N, with
N sampled just above the current best half-order (best_n / 2), biased toward the smallest feasible
orders, since smaller groups are easier to cover.

Every zero-cost set is turned into a Haar graph and checked with lib.is_valid before it is accepted.
If nothing beats the fallback, the verified 3582-vertex Haar graph is returned.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10

# Valid Haar fallback (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]

HI_HALF = 2010  # largest group order tried (record corresponds to order 2000)


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j and (a, j)(b, l) = (a + r^j b, j + l).

    Returns (MT, inv), where MT[x, y] = x*y and inv[x] is the inverse of x.
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


def random_group(N, rng):
    """Random non-abelian metacyclic group (m, k, r) of order N, or None if none is found quickly."""
    divs = [m for m in range(3, N) if N % m == 0 and N // m >= 2]
    if not divs:
        return None
    for idx in rng.permutation(len(divs)):
        m = divs[int(idx)]
        k = N // m
        for _ in range(60):
            r = int(rng.integers(2, m))
            if r != 1 and math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                return m, k, r
    return None


# ------------------------------------------------------------------------------ cost

def cover_cost(S, MT, inv, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2 in G (zero iff the Haar graph has diameter <= 5).

    S is an int64 array of distinct group elements. The two squares are computed with
    gathers on MT and a boolean mark array.
    """
    Si = inv[S]
    total = 0
    for P in (MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()):
        A = np.unique(P)
        mark = np.zeros(N, dtype=bool)
        mark[MT[np.ix_(A, A)].ravel()] = True
        total += N - int(np.count_nonzero(mark))
    return total


def anneal(N, MT, inv, d, rng, deadline, steps, K=8):
    """Annealing over connection sets; returns a zero-cost set S, or None."""
    S = rng.choice(N, d, replace=False).astype(np.int64)
    cur = cover_cost(S, MT, inv, N)
    for step in range(steps):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = 0.6 * (1.0 - step / steps) + 0.05
        best_c, best_T = None, None
        for _ in range(K):
            pos = int(rng.integers(d))
            g = int(rng.integers(N))
            if g in S:
                continue
            T = S.copy()
            T[pos] = g
            c = cover_cost(T, MT, inv, N)
            if best_c is None or c < best_c:
                best_c, best_T = c, T
        if best_T is None:
            continue
        if best_c <= cur or rng.random() < math.exp(-(best_c - cur) / temp):
            S, cur = best_T, best_c
    return S if cur == 0 else None


def haar_from(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N + g, and (g, A) ~ (s*g, B) for s in S."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


# ------------------------------------------------------------------------------ build

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

    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        hi = max(lo, HI_HALF)
        # Bias toward the smallest feasible orders, since they are easiest to cover.
        N = lo + int((rng.random() ** 2) * (hi - lo + 1))
        N = min(N, hi)
        grp = random_group(N, rng)
        if grp is None:
            continue
        m, k, r = grp
        try:
            MT, inv = group_table(m, k, r)
        except Exception:
            continue
        S = anneal(N, MT, inv, d, rng, deadline, steps=2500)
        if S is None:
            continue
        n, e = haar_from(MT, S, N)
        if n <= best_n:
            continue
        try:
            ok = lib.is_valid(n, e, d, D)
        except Exception:
            ok = False
        if ok:
            best_n, best_edges = n, e

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
