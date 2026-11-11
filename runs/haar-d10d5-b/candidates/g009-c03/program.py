"""Haar-graph search for the diameter-5 target with a closed-form cover cost.

NEW IDEA: a fast exact cost for Haar graphs. For a group G of order N and a connection set S of size d, the Haar
graph on 2N vertices has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. Both sets can be computed directly
from the group multiplication table: the words s^-1 s' and s s'^-1 give d^2 elements each, and their pairwise
products give d^4 elements. So cost(S) = uncovered elements, which costs about 100 microseconds with numpy. The
parent's BFS cost over all 2pN vertices is far slower. This allows many more annealing steps per second.

SEARCH. Round-robin simulated annealing over S, one random replacement per step, with Metropolis acceptance and
restarts. Tasks use random non-abelian metacyclic groups of orders just above the best known half-order. Any
zero-cost S is rebuilt as an explicit Haar graph and checked with lib.is_valid before it is accepted. A valid
fallback (2*1791 = 3582 vertices) is always kept, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
POOL = 6

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


def random_group(N, rng):
    """A random metacyclic group of order N, non-abelian when possible. Returns (MT, inv)."""
    cands = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m and r % m != 1:
                cands.append((m, k, r))
    if not cands:
        return group_table(1, N, 1)  # cyclic fallback
    m, k, r = cands[int(rng.integers(len(cands)))]
    return group_table(m, k, r)


# ------------------------------------------------------------------------------ cost

def cover_cost(S, MT, invtab, N):
    """Uncovered elements for (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    iS = invtab[S]
    P = MT[iS[:, None], S[None, :]].ravel()
    P2 = MT[P[:, None], P[None, :]].ravel()
    Q = MT[S[:, None], iS[None, :]].ravel()
    Q2 = MT[Q[:, None], Q[None, :]].ravel()
    c1 = np.count_nonzero(np.bincount(P2, minlength=N))
    c2 = np.count_nonzero(np.bincount(Q2, minlength=N))
    return 2 * N - c1 - c2


def search_gen(N, MT, invtab, d, rng):
    """Generator: one annealing step per yield. Yields ('found', S) at cost 0, then ends."""
    while True:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        cur = cover_cost(S, MT, invtab, N)
        if cur == 0:
            yield ('found', S.copy())
            return
        L = 20000
        for step in range(L):
            i = int(rng.integers(d))
            g = int(rng.integers(N))
            if np.any(S == g):
                yield None
                continue
            old = S[i]
            S[i] = g
            c = cover_cost(S, MT, invtab, N)
            temp = 0.05 + 1.5 * (1.0 - step / L)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
                if cur == 0:
                    yield ('found', S.copy())
                    return
            else:
                S[i] = old
            yield None


def spawn(best_half, rng, d):
    """A fresh search task over a group whose order exceeds best_half."""
    N = best_half + 1 + int(rng.integers(0, 12))
    MT, invtab = random_group(N, rng)
    gen = search_gen(N, MT, invtab, d, rng)
    return {'gen': gen, 'N': N, 'MT': MT}


def haar_from(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N + g; A_g ~ B_{s*g} for s in S."""
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

    pool = [spawn(best_n // 2, rng, d) for _ in range(POOL)]
    while time.monotonic() < deadline:
        for idx in range(len(pool)):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            if 2 * task['N'] <= best_n:
                pool[idx] = spawn(best_n // 2, rng, d)
                continue
            try:
                out = next(task['gen'])
            except Exception:
                pool[idx] = spawn(best_n // 2, rng, d)
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
                pool[idx] = spawn(best_n // 2, rng, d)

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
