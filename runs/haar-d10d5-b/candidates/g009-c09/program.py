"""Bold variant for d=10, D=5: 4-orbit voltage lifts instead of Haar graphs.

Base graph: two A-orbits and two B-orbits (K_{2,2} with multiplicities m_uv, rows and columns summing to d).
Each base dart (u, v, g) lifts to (u, x) ~ (v, x*g) over a metacyclic group G of order about 1000-1040, giving
4|G| vertices of degree d. The left action of G is by automorphisms, so distances from the four identity
vertices (u, e) determine all distances. The cost is the number of vertices unreached within D steps from those
four sources, and cost 0 means valid. Annealing moves replace one voltage at a time (distinct voltages per base
pair keep the graph simple). Every candidate is checked with lib.is_valid. The parent's valid Haar graph
(3582 vertices) is the fallback, and trivial() is the last resort, so every case still returns a valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)

# Base multiplicity matrices m[u][v] for d = 10 (each row and each column sums to 10).
CONFIGS = [
    ((5, 5), (5, 5)),
    ((6, 4), (4, 6)),
    ((4, 6), (6, 4)),
    ((7, 3), (3, 7)),
    ((3, 7), (7, 3)),
]


def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def meta_candidates(lo, hi, cap):
    """Metacyclic groups Z_m x| Z_k (non-abelian, lam != 1) with order in [lo, hi], smallest orders first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, 13):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lams = [x for x in range(2, m) if math.gcd(x, m) == 1 and pow(x, k, m) == 1]
            if lams:
                out.append((m, k, lams[0]))
                if len(out) >= cap:
                    return out
    return out


def lift_nb(MT, V, d):
    """Adjacency (4N, d) of the 4-orbit lift. Orbits: A0 = 0, A1 = 1, B0 = 2, B1 = 3 (blocks of size N)."""
    N = MT.shape[0]
    xs = np.arange(N, dtype=np.int64)
    nb = np.empty((4 * N, d), dtype=np.int64)
    col = [0, 0, 0, 0]
    for u, v, volts in V:
        bs = 2 + v
        for g in volts:
            a_idx = u * N + xs
            b_idx = bs * N + MT[xs, int(g)].astype(np.int64)
            nb[a_idx, col[u]] = b_idx
            nb[b_idx, col[bs]] = a_idx
            col[u] += 1
            col[bs] += 1
    return nb


def lift_graph(MT, V, d):
    """(n, edges) of the lift: A-vertices are 0..2N-1, B-vertices are 2N..4N-1."""
    N = MT.shape[0]
    nb = lift_nb(MT, V, d)
    edges = [(a, b) for a in range(2 * N) for b in nb[a].tolist()]
    return 4 * N, edges


def lift_search(MT, d, D, deadline, rng, patience=3000):
    """Annealing over voltages. Returns a voltage state V of cost 0, or None if the deadline passes."""
    N = MT.shape[0]
    src = np.arange(4, dtype=np.int64) * N

    def cost(V):
        nb = lift_nb(MT, V, d)
        R = np.zeros((4, 4 * N), dtype=bool)
        R[np.arange(4), src] = True
        for _ in range(D):
            R = R | R[:, nb].any(axis=2)
        return int(np.count_nonzero(~R))

    def init(cfg):
        V = []
        for u in range(2):
            for v in range(2):
                m_uv = cfg[u][v]
                volts = rng.choice(N, m_uv, replace=False).astype(np.int64)
                V.append([u, v, volts])
        return V

    while time.monotonic() < deadline:
        cfg = CONFIGS[int(rng.integers(len(CONFIGS)))]
        V = init(cfg)
        cur = cost(V)
        since = 0
        T = 1.0
        while cur > 0 and since < patience and time.monotonic() < deadline:
            p = int(rng.integers(len(V)))
            volts = V[p][2]
            s = int(rng.integers(len(volts)))
            g = int(rng.integers(N))
            if np.any(volts == g):
                since += 1
                continue
            old = volts[s]
            volts[s] = g
            c = cost(V)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                since = 0 if delta < 0 else since + 1
            else:
                volts[s] = old
                since += 1
        if cur == 0:
            return V
    return None


def haar_from(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, edges (g, A) ~ (s*g, B) for s in S."""
    N = MT.shape[0]
    g = np.arange(N)
    S = sorted({int(s) for s in S})
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    if D >= 2 and d >= 1:
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    return 1, []


def solve(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.6 * time_limit
    rng = np.random.default_rng(seed)
    best, best_n = None, 0

    # Fallback: the parent's valid Haar graph (order 3582).
    try:
        MT, _ = group_meta(199, 9, 180)
        S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
        n, edges = haar_from(MT, S)
        if lib.is_valid(n, edges, d, D):
            best, best_n = (n, edges), n
    except Exception:
        pass

    # Bold search: 4-orbit voltage lifts over metacyclic groups of order just above 1000.
    cands = meta_candidates(1001, 1040, 6)
    for idx, (m, k, lam) in enumerate(cands):
        now = time.monotonic()
        remaining = end - now
        if remaining <= 2.0:
            break
        slot_end = now + remaining / (len(cands) - idx)
        try:
            MT, _ = group_meta(m, k, lam)
            V = lift_search(MT, d, D, slot_end, rng)
            if V is None:
                continue
            n, edges = lift_graph(MT, V, d)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best, best_n = (n, edges), n
        except Exception:
            continue

    if best is None:
        return trivial(d, D)
    return best


def build(d, D, seed, time_limit):
    try:
        if (d, D) != TARGET:
            return trivial(d, D)
        return solve(d, D, seed, time_limit)
    except Exception:
        return trivial(d, D)
