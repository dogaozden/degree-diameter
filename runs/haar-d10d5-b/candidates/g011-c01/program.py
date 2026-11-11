"""Haar-graph search for the bipartite degree-diameter target (d=10, D=5).

CONSTRUCTION.  Take a group G of order N and a connection set S of d = 10 elements.  The Haar graph has
vertices (g, A) and (g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular,
and has 2N vertices.  Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  The cost is the number of group elements missing from those two squares.  Its evaluation uses only
d^2-sized products and a boolean mark array, so one step costs about 0.1 ms, much faster than a BFS over the
whole graph.  Simulated annealing replaces one element of S per step.  Groups are metacyclic Z_m x|_r Z_k of
order N in a window just above 2000 (so the graph has more than 4000 vertices), and non-abelian groups are
preferred.  Each candidate is confirmed with lib.is_valid before it is accepted.  The valid Haar graph of order
3582 is kept as the fallback.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
D_DEG = 10
FLOOR_N = 2000          # search for group orders N > FLOOR_N, giving 2N > 4000 vertices
WINDOW = 30             # sample group orders in (floor, floor + WINDOW]
STEPS = 8000            # annealing steps per restart
RESTARTS_PER_GROUP = 6

# Valid Haar fallback (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
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


_OPTS_CACHE = {}


def opts_for(N):
    """All nontrivial metacyclic presentations (m, k, r) of order N, cached."""
    if N in _OPTS_CACHE:
        return _OPTS_CACHE[N]
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
    _OPTS_CACHE[N] = out
    return out


def pick_config(N, rng):
    """A random non-abelian metacyclic group of order N, or the cyclic group if none exists."""
    opts = opts_for(N)
    if opts:
        return opts[int(rng.integers(len(opts)))]
    return (N, 1, 1)


def haar_cost(MT, inv, S, N, mark):
    """Number of elements missing from (S^-1 S)^2 plus those missing from (S S^-1)^2."""
    iS = inv[S]
    A = MT[iS[:, None], S[None, :]].ravel()   # S^-1 S
    B = MT[S[:, None], iS[None, :]].ravel()   # S S^-1
    c = 0
    for X in (A, B):
        X = np.unique(X)
        Q = MT[X[:, None], X[None, :]].ravel()
        mark[:] = False
        mark[Q] = True
        c += N - int(np.count_nonzero(mark))
    return c


def anneal(MT, inv, N, rng, mark, steps, deadline):
    """Simulated annealing over S.  Returns a cost-0 connection set (int64 array) or None."""
    S = rng.choice(N, D_DEG, replace=False).astype(np.int64)
    cur = haar_cost(MT, inv, S, N, mark)
    for step in range(steps):
        if cur == 0:
            return S
        if step % 256 == 0 and time.monotonic() >= deadline:
            break
        i = int(rng.integers(D_DEG))
        g = int(rng.integers(N))
        if np.any(S == g):
            continue
        old = int(S[i])
        S[i] = g
        c = haar_cost(MT, inv, S, N, mark)
        T = 0.4 + 1.6 * (1.0 - step / steps)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            S[i] = old
    return S if cur == 0 else None


def haar_edges(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), A-vertex g is g, B-vertex g is N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in S:
        edges.extend(zip(ar.tolist(), (N + MT[int(s)].astype(np.int64)).tolist()))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 8.0))
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

    floor_N = FLOOR_N
    while time.monotonic() < deadline:
        N = floor_N + 1 + int(rng.integers(WINDOW))
        m, k, r = pick_config(N, rng)
        try:
            MT, inv = group_table(m, k, r)
        except Exception:
            continue
        mark = np.zeros(N, dtype=bool)
        for _ in range(RESTARTS_PER_GROUP):
            if time.monotonic() >= deadline:
                break
            S = anneal(MT, inv, N, rng, mark, STEPS, deadline)
            if S is None:
                continue
            try:
                n, e = haar_edges(MT, S, N)
                ok = n > best_n and lib.is_valid(n, e, d, D)
            except Exception:
                ok = False
            if ok:
                best_n, best_edges = n, e
                floor_N = max(floor_N, N)
                break

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
