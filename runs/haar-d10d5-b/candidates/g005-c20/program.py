"""Haar-graph annealing for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a finite group G of order N and a connection set S of d distinct elements.  The Haar graph has
vertices A_g and B_g (g in G) and edges A_g ~ B_{s*g} for s in S.  It is bipartite, d-regular, has 2N vertices, and
right multiplication is an automorphism, so each side is vertex-transitive.  Its diameter is at most 5 iff
T^2 = G and U^2 = G, where T = S^-1 S and U = S S^-1 (both contain the identity).  So
cost(S) = (N - |T^2|) + (N - |U^2|), and a zero cost gives a valid graph on 2N vertices.

SEARCH.  Non-abelian metacyclic groups Z_m x| Z_k with orders N just above the current best/2 (a valid graph needs
2N > 3582 to improve, and 2N > 4000 to beat the record).  Simulated annealing replaces one element of S per move.
Several group/annealing tasks run round-robin, and the group window moves up whenever a valid graph is found.
Every zero-cost result is checked with lib.is_valid before it is accepted.  The parent's valid Haar graph on 3582
vertices is the fallback, so the output is never worse than before.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
POOL = 4
STEPS = 5000
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


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


def pick_group(N, rng):
    """A random NON-abelian metacyclic group of order N as (MT, inv), or None if none exists."""
    opts = []
    for m in range(3, N // 2 + 1):
        if N % m:
            continue
        k = N // m
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                opts.append((m, k, r))
    if not opts:
        return None
    m, k, r = opts[int(rng.integers(len(opts)))]
    return group_table(m, k, r)


# ------------------------------------------------------------------------------ search

def make_cost(MT, inv, N):
    """cost(S) = number of elements missing from T^2 plus those missing from U^2."""
    def cost(S):
        Si = inv[S]
        P = MT[Si[:, None], S[None, :]].ravel()          # s_i^-1 s_j
        T2 = MT[P[:, None], P[None, :]].ravel()
        Q = MT[S[:, None], Si[None, :]].ravel()          # s_i s_j^-1
        U2 = MT[Q[:, None], Q[None, :]].ravel()
        covered = (np.count_nonzero(np.bincount(T2, minlength=N))
                   + np.count_nonzero(np.bincount(U2, minlength=N)))
        return 2 * N - int(covered)
    return cost


def anneal_gen(MT, inv, N, d, rng):
    """Generator: one annealing step per yield.  Yields ('found', S) on cost 0, then ends."""
    cost = make_cost(MT, inv, N)
    while True:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        cur = cost(S)
        if cur == 0:
            yield ('found', S.copy())
            return
        for step in range(STEPS):
            t = int(rng.integers(d))
            new = int(rng.integers(N))
            if np.any(S == new):
                yield None
                continue
            old = int(S[t])
            S[t] = new
            c = cost(S)
            temp = 0.4 + 1.2 * (1.0 - step / STEPS)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
                if cur == 0:
                    yield ('found', S.copy())
                    return
            else:
                S[t] = old
            yield None
        # Stuck for STEPS steps: restart S in the same group.


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

    def spawn():
        """A fresh task whose Haar graph has more than best_n vertices (group order > best_n / 2)."""
        lo = best_n // 2 + 1 if best_n else 1000
        hi = lo + 60
        for _ in range(200):
            N = int(rng.integers(lo, hi + 1))
            res = pick_group(N, rng)
            if res is not None:
                MT, inv = res
                return {'gen': anneal_gen(MT, inv, N, d, rng), 'N': N, 'MT': MT}
        return None

    pool = [spawn() for _ in range(POOL)]
    while time.monotonic() < deadline:
        for idx in range(POOL):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            if task is None or 2 * task['N'] <= best_n:
                pool[idx] = spawn()
                continue
            try:
                out = next(task['gen'])
            except Exception:
                pool[idx] = spawn()
                continue
            if out is not None:
                N = task['N']
                try:
                    n, edges = haar_from(task['MT'], out[1], N)
                    ok = n > best_n and lib.is_valid(n, edges, d, D)
                except Exception:
                    ok = False
                if ok:
                    best_n, best_edges = n, edges
                pool[idx] = spawn()

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
