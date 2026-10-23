"""Haar-graph search for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a finite group G of order N and a connection set S of d elements.  The Haar graph has
vertices A_g and B_g (g in G), with edges A_g ~ B_{s*g} for s in S.  It is bipartite, d-regular and has 2N
vertices.  Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  The cost counts the uncovered elements of G in those two squared sets.  The search is simulated annealing
over S, with random restarts over several non-abelian metacyclic groups Z_m x|_r Z_k of order N, where N sits
just above the current best threshold (N > best_n / 2).  Every zero-cost graph is checked with lib.is_valid before
it is accepted.  A valid Haar graph (2*1791 = 3582 vertices) is the fallback, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
WINDOW = 80          # candidate group orders are sampled from [lo, lo + WINDOW)
STEPS = 3000         # annealing steps per restart

# Valid Haar fallback from the parent (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
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


def nonabelian_metacyclic(N):
    """All (m, k, r) with m*k = N, k >= 2, r != 1 (non-abelian Z_m x|_r Z_k)."""
    out = []
    for m in range(3, N // 2 + 1):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def haar_cost(MT, inv, S, N):
    """2N minus |(S^-1 S)^2| minus |(S S^-1)^2|; zero exactly when the Haar graph has diameter <= 5."""
    iS = inv[S]
    X = np.unique(MT[iS[:, None], S[None, :]])        # S^-1 S
    Y = np.unique(MT[S[:, None], iS[None, :]])        # S S^-1
    X2 = np.unique(MT[X[:, None], X[None, :]])
    Y2 = np.unique(MT[Y[:, None], Y[None, :]])
    return 2 * N - X2.size - Y2.size


def anneal(MT, inv, N, d, rng, steps, deadline):
    """Annealing over connection sets S of size d.  Returns a zero-cost S, or None."""
    S = rng.choice(N, d, replace=False).astype(np.int64)
    cur = haar_cost(MT, inv, S, N)
    for step in range(steps):
        if cur == 0:
            return S
        if time.monotonic() >= deadline:
            return None
        i = int(rng.integers(d))
        g = int(rng.integers(N))
        if np.any(S == g):
            continue
        old = int(S[i])
        S[i] = g
        c = haar_cost(MT, inv, S, N)
        T = 1.0 * (1.0 - step / steps) + 0.05
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            S[i] = old
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
    deadline = t0 + max(2.0, min(0.80 * time_limit, time_limit - 8.0))
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
        N = lo + int(rng.integers(0, WINDOW))
        choices = nonabelian_metacyclic(N)
        if not choices:
            continue
        m, k, r = choices[int(rng.integers(len(choices)))]
        try:
            MT, inv = group_table(m, k, r)
            S = anneal(MT, inv, m * k, d, rng, STEPS, deadline)
        except Exception:
            continue
        if S is None:
            continue
        n_c, edges = haar_from(MT, S, m * k)
        if n_c > best_n:
            try:
                ok = lib.is_valid(n_c, edges, d, D)
            except Exception:
                ok = False
            if ok:
                best_n, best_edges = n_c, edges

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
