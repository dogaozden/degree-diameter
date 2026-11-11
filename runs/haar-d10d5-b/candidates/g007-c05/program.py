"""Haar-graph search over non-abelian metacyclic groups for the d=10, D=5 target.

CONSTRUCTION.  A Haar graph over a finite group G with connection set S (|S| = d) has vertices (g, A) and
(g, B), with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite and d-regular on 2|G| vertices.  Its diameter
is at most 5 when (S^-1 S)^2 = G and (S S^-1)^2 = G.  The cost of a set S is the number of group elements
missing from those two sets.  A zero-cost S gives a valid graph.

GROUPS.  Non-abelian metacyclic groups Z_m x|_r Z_k with m*k = N, for N just above 2000.  A graph on 2N vertices
beats the record (4000) only when N >= 2001.

SEARCH.  Simulated annealing on S, one slot replaced per step, with restarts when stalled.  A small pool of
(group, N) tasks runs round-robin in short slices.  Any zero-cost S is rebuilt as a Haar graph and checked with
lib.is_valid before it is accepted.  The valid Haar graph from the parent (3582 vertices) is the fallback.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
POOL = 6
SLICE = 3.0
N_START = 2001

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


def options(N):
    """Non-abelian metacyclic groups (m, k, r) of order N, with m >= 3 and k >= 2."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def cost(S, MT, inv, N):
    """Number of group elements missing from (S^-1 S)^2 and from (S S^-1)^2."""
    Sinv = inv[S]
    A = MT[Sinv[:, None], S[None, :]].ravel()
    B = MT[A[:, None], A[None, :]].ravel()
    mark = np.zeros(N, dtype=bool)
    mark[B] = True
    c1 = N - int(np.count_nonzero(mark))
    Q = MT[S[:, None], Sinv[None, :]].ravel()
    C = MT[Q[:, None], Q[None, :]].ravel()
    mark = np.zeros(N, dtype=bool)
    mark[C] = True
    c2 = N - int(np.count_nonzero(mark))
    return c1 + c2


def search(N, MT, inv, d, rng, end):
    """Annealing with restarts until zero cost (returns S) or the time slice ends (returns None)."""
    while time.monotonic() < end:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        c = cost(S, MT, inv, N)
        stall = 0
        while c > 0 and stall <= 3000 and time.monotonic() < end:
            i = int(rng.integers(d))
            g = int(rng.integers(N))
            if (S == g).any():
                stall += 1
                continue
            old = int(S[i])
            S[i] = g
            c2 = cost(S, MT, inv, N)
            temp = 0.7
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
                stall = 0 if c2 < c else stall + 1
                c = c2
            else:
                S[i] = old
                stall += 1
        if c == 0:
            return S
    return None


def haar_from(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), vertices A = g, B = N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


def make_task(N, rng):
    """A (N, group) task with a non-abelian group of order N, or None if there is none."""
    opts = options(N)
    if not opts:
        return None
    m, k, r = opts[int(rng.integers(len(opts)))]
    return {'N': N, 'm': m, 'k': k, 'r': r, 'MT': None, 'inv': None}


def fill_tasks(start, count, rng):
    """Up to `count` tasks with N >= start (N is searched upward from start)."""
    tasks = []
    N = start
    while len(tasks) < count and N < start + 400:
        t = make_task(N, rng)
        if t is not None:
            tasks.append(t)
        N += 1
    return tasks


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

    pool = fill_tasks(N_START, POOL, rng)
    while time.monotonic() < deadline and pool:
        for idx in range(len(pool)):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            N = task['N']
            if 2 * N <= best_n:
                new = fill_tasks(best_n // 2 + 1, 1, rng)
                if new:
                    pool[idx] = new[0]
                continue
            try:
                if task['MT'] is None:
                    MT, inv = group_table(task['m'], task['k'], task['r'])
                    task['MT'], task['inv'] = MT, inv
                end = min(deadline, time.monotonic() + SLICE)
                S = search(N, task['MT'], task['inv'], d, rng, end)
                if S is not None:
                    n, e = haar_from(task['MT'], S, N)
                    if n > best_n and lib.is_valid(n, e, d, D):
                        best_n, best_edges = n, e
                        new = fill_tasks(best_n // 2 + 1, 1, rng)
                        if new:
                            pool[idx] = new[0]
                        continue
                task['MT'] = None
                task['inv'] = None
            except Exception:
                new = fill_tasks(best_n // 2 + 1, 1, rng)
                if new:
                    pool[idx] = new[0]

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
