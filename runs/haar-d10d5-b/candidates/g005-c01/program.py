"""Haar-graph covering search over metacyclic groups of order just above 1791 (d=10, D=5).

NEW IDEA (this variant).  A Haar graph on a group G with connection set S (|S| = d) has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  The cost of S is the number of uncovered group elements in those two
squares.  This program searches for zero-cost S directly, using a vectorised cost (about 10^4 table gathers
per evaluation) and an annealing move that swaps one element of S.  Instead of fixing one group, it samples
random non-abelian metacyclic groups Z_m x|_r Z_k with orders 2N in (best_n, best_n + ~400], so the search
covers many groups near the target order.

Every candidate is checked with lib.is_valid before acceptance.  The verified Haar graph of order 3582 from
the parent is the starting fallback, so the output never gets worse.
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


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j and (a, j)(b, l) = (a + r^j b, j + l).

    Returns (MT, inv): MT[x, y] = x*y and inv[x] = x^{-1}.
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
    """All (m, k, r) with m*k = N, k >= 2, r != 1 (non-abelian), gcd(r, m) = 1, r^k = 1 mod m."""
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

def cost(S, MT, inv, N):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2.  Zero iff diameter <= 5."""
    iS = inv[S]
    X = np.unique(MT[iS[:, None], S[None, :]])
    mask = np.zeros(N, dtype=bool)
    mask[MT[X[:, None], X[None, :]]] = True
    c = N - int(np.count_nonzero(mask))
    Y = np.unique(MT[S[:, None], iS[None, :]])
    mask[:] = False
    mask[MT[Y[:, None], Y[None, :]]] = True
    c += N - int(np.count_nonzero(mask))
    return c


def anneal(MT, inv, N, d, rng, deadline, L=3000, restarts=6):
    """Annealing over connection sets S with single-element swaps.  Returns a zero-cost S or None."""
    for _ in range(restarts):
        S = rng.choice(N, d, replace=False).astype(np.int64)
        cur = cost(S, MT, inv, N)
        for step in range(L):
            if cur == 0:
                return S.copy()
            if time.monotonic() > deadline:
                return None
            i = int(rng.integers(d))
            g = int(rng.integers(N))
            if np.any(S == g):
                continue
            old = S[i]
            S[i] = g
            c = cost(S, MT, inv, N)
            temp = 1.0 * (1.0 - step / L) + 0.15
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                S[i] = old
        if cur == 0:
            return S.copy()
    return None


# ------------------------------------------------------------------------------ lift

def haar_from(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), vertices A = g, B = N + g."""
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

    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        N = int(rng.integers(lo, lo + 401))
        opts = metacyclic_options(N)
        if not opts:
            continue
        m, k, r = opts[int(rng.integers(len(opts)))]
        try:
            MT, inv = group_table(m, k, r)
        except Exception:
            continue
        S = anneal(MT, inv, N, d, rng, deadline)
        if S is None:
            continue
        try:
            n, e = haar_from(MT, S, N)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_edges = n, e
        except Exception:
            pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
