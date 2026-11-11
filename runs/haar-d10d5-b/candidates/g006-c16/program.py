"""Directed Haar-graph search for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Haar graph H(G, S) on 2N vertices: A_g ~ B_{s*g} for s in S, |S| = d, G a finite group.
Right multiplication is an automorphism, so the diameter is <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.
Both covering conditions are checked from the d^2 "difference" elements, so the cost of a set S is cheap.

NEW IDEA (directed moves).  Instead of replacing a slot at random, the search reads the uncovered elements
u of (S^-1 S)^2 and (S S^-1)^2 and builds a slot value that puts u into the difference set:
  - to cover u as s^-1 s_j, set s = s_j * u^-1;
  - to cover u as s * s_j^-1, set s = u * s_j.
Random, product (s_j * s_k) and directed moves are mixed, with Metropolis acceptance and restarts.

GROUPS.  Metacyclic groups Z_m x|_r Z_k, non-abelian (r != 1), with N just above best_n/2, so each
success raises the target order.  Every result is checked with lib.is_valid.  A valid Haar graph of
order 3582 is the fallback, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
POOL = 4
CHUNK = 400
RESTART_AFTER = 15000
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


def nonabelian_options(N):
    """All (m, k, r) with m*k = N, k >= 2, r a unit of order dividing k acting nontrivially."""
    out = []
    for m in range(3, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def evaluate(S, MT, inv):
    """Return (cost, uncovered elements of (S^-1 S)^2, uncovered elements of (S S^-1)^2)."""
    N = MT.shape[0]
    Si = inv[S]
    Q = np.unique(MT[Si[:, None], S[None, :]].ravel())
    R = np.unique(MT[S[:, None], Si[None, :]].ravel())
    mq = np.zeros(N, dtype=bool)
    mq[MT[Q[:, None], Q[None, :]].ravel()] = True
    mr = np.zeros(N, dtype=bool)
    mr[MT[R[:, None], R[None, :]].ravel()] = True
    uq = np.nonzero(~mq)[0]
    ur = np.nonzero(~mr)[0]
    return len(uq) + len(ur), uq, ur


def haar_edges(MT, S, N):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N + g; A_g ~ B_{s*g}."""
    S = np.asarray(S, dtype=np.int64)
    A = np.tile(np.arange(N, dtype=np.int64), len(S))
    B = N + MT[S].astype(np.int64).ravel()
    return list(zip(A.tolist(), B.tolist()))


class Task:
    def __init__(self, N, MT, inv, rng, d):
        self.N = N
        self.MT = MT
        self.inv = inv
        self.reset(rng, d)

    def reset(self, rng, d):
        self.S = rng.choice(self.N, d, replace=False).astype(np.int64)
        self.cur, self.uq, self.ur = evaluate(self.S, self.MT, self.inv)
        self.age = 0


def new_task(rng, best_n, d):
    """A fresh Haar search over a non-abelian metacyclic group of order N > best_n / 2."""
    opts = []
    N = 0
    for _ in range(200):
        lo = best_n // 2 + 1
        N = int(rng.integers(lo, lo + 260))
        opts = nonabelian_options(N)
        if opts:
            break
    if not opts:
        return None
    m, k, r = opts[int(rng.integers(len(opts)))]
    MT, inv = group_table(m, k, r)
    return Task(N, MT, inv, rng, d)


def run(task, rng, steps, d):
    """Run up to `steps` annealing moves. Returns a zero-cost S (copy) or None."""
    MT, inv, N = task.MT, task.inv, task.N
    S = task.S
    for _ in range(steps):
        task.age += 1
        if task.age > RESTART_AFTER:
            task.reset(rng, d)
            return None
        i = int(rng.integers(d))
        old = int(S[i])
        nq, nr = len(task.uq), len(task.ur)
        x = rng.random()
        if x < 0.45 and nq + nr > 0:
            # directed move: put an uncovered element into a difference set
            j = int(rng.integers(d))
            if int(rng.integers(nq + nr)) < nq:
                u = int(task.uq[int(rng.integers(nq))])
                new = int(MT[S[j], inv[u]])
            else:
                u = int(task.ur[int(rng.integers(nr))])
                new = int(MT[u, S[j]])
        elif x < 0.55:
            j, kk = (int(v) for v in rng.integers(d, size=2))
            new = int(MT[S[j], S[kk]])
        else:
            new = int(rng.integers(N))
        if new == old or np.any(S == new):
            continue
        S[i] = new
        c, uq, ur = evaluate(S, MT, inv)
        T = 0.2 + 1.0 * (1.0 - task.age / RESTART_AFTER)
        if c <= task.cur or rng.random() < math.exp(-(c - task.cur) / T):
            task.cur, task.uq, task.ur = c, uq, ur
            if c == 0:
                return S.copy()
        else:
            S[i] = old
    return None


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
        S0 = np.array(FALLBACK_S, dtype=np.int64)
        n = 2 * m * k
        e = haar_edges(MT, S0, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    tasks = []
    while len(tasks) < POOL:
        t = new_task(rng, best_n, d)
        if t is None:
            break
        tasks.append(t)

    while time.monotonic() < deadline and tasks:
        for idx in range(len(tasks)):
            if time.monotonic() >= deadline:
                break
            task = tasks[idx]
            if 2 * task.N <= best_n:
                t = new_task(rng, best_n, d)
                if t is not None:
                    tasks[idx] = t
                continue
            try:
                found = run(task, rng, CHUNK, d)
            except Exception:
                found = None
                task.reset(rng, d)
            if found is None:
                continue
            n = 2 * task.N
            ok = False
            try:
                edges = haar_edges(task.MT, found, task.N)
                ok = n > best_n and lib.is_valid(n, edges, d, D)
            except Exception:
                ok = False
            if ok:
                best_n, best_edges = n, edges
            else:
                task.reset(rng, d)

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
