"""Bold variant for the bipartite degree-diameter target (d=10, D=5): Haar graphs over metacyclic groups.

CONSTRUCTION.  Take a non-abelian metacyclic group G = Z_m x|_r Z_k of order N and a connection set S of d
distinct group elements.  Vertices (g, A) and (g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.
The graph is bipartite, d-regular, and has 2N vertices.  It has diameter <= 5 when
(S^-1 S)^2 = G and (S S^-1)^2 = G.  The cost counts the uncovered elements of these two sets.

SEARCH.  Simulated annealing on S: replace one element per move and accept by the Metropolis rule.  Several
annealing tasks run round-robin over group orders N just above the current best.  Every zero-cost set is
expanded to a graph and checked with lib.is_valid before it is accepted.

FALLBACK.  The valid Haar graph of order 3582 from the parent is built and checked first, so the output is
never worse than the parent's.  Other (d, D) cases use the trivial construction.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
POOL = 4
WINDOW = 80
RESTART = 6000

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


def nonabelian(N, rng):
    """Return (m, k, r) for a non-abelian metacyclic group of order N, or None."""
    divs = [m for m in range(2, N) if N % m == 0 and N // m >= 2]
    if not divs:
        return None
    for m in rng.permutation(divs).tolist():
        k = N // m
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            return m, k, rs[int(rng.integers(len(rs)))]
    return None


def haar_edges(MT, S, N):
    """Haar graph: (g, A) ~ (s*g, B), with A-vertex g = g and B-vertex g = N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


def cover_cost(S, MT, inv, N):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2."""
    iS = inv[S]
    total = 0
    for D in (MT[iS[:, None], S[None, :]].ravel(), MT[S[:, None], iS[None, :]].ravel()):
        P = MT[D[:, None], D[None, :]].ravel()
        total += N - int(np.count_nonzero(np.bincount(P, minlength=N)))
    return total


def anneal(MT, inv, N, d, rng):
    """Generator: one annealing step per yield.  Yields ('found', S) at cost 0 and then continues."""
    while True:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        cur = cover_cost(S, MT, inv, N)
        for step in range(RESTART):
            if cur == 0:
                yield ('found', S.copy())
                break
            i = int(rng.integers(d))
            x = int(rng.integers(N))
            if np.any(S == x):
                yield None
                continue
            old = int(S[i])
            S[i] = x
            c = cover_cost(S, MT, inv, N)
            temp = 0.6 * (1.0 - step / RESTART) + 0.05
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                S[i] = old
            yield None


def spawn(best_N, rng, d):
    """A fresh annealing task over a group of order N in (best_N, best_N + WINDOW]."""
    for _ in range(200):
        N = int(rng.integers(best_N + 1, best_N + WINDOW + 1))
        g = nonabelian(N, rng)
        if g is None:
            continue
        m, k, r = g
        MT, inv = group_table(m, k, r)
        return {'N': N, 'MT': MT, 'inv': inv, 'gen': anneal(MT, inv, N, d, rng)}
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + max(3.0, min(0.80 * time_limit, time_limit - 8.0))
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

    best_N = best_n // 2
    pool = [spawn(best_N, rng, d) for _ in range(POOL)]
    while time.monotonic() < deadline:
        for idx in range(len(pool)):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            if task is None or task['N'] <= best_N:
                pool[idx] = spawn(best_N, rng, d)
                continue
            try:
                out = next(task['gen'])
            except Exception:
                pool[idx] = spawn(best_N, rng, d)
                continue
            if out is None:
                continue
            N = task['N']
            try:
                n, e = haar_edges(task['MT'], out[1], N)
                ok = n > best_n and lib.is_valid(n, e, d, D)
            except Exception:
                ok = False
            if ok:
                best_n, best_edges = n, e
                best_N = N
            pool[idx] = spawn(best_N, rng, d)

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
