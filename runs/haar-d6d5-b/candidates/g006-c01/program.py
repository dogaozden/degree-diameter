"""Two-orbit group lifts for the (d=6, D=5) target, with dense-matrix cost evaluation and a verified Haar fallback.

CONSTRUCTION.  Take a group G of order M and four vertex orbits: A-orbits 0, 1 and B-orbits 2, 3.
Vertex (o, x) has id o*M + x.  A dart (i, j, g) joins (i, x) to (2+j, x*g) for every x in G.  Each
A-orbit has 6 darts out and each B-orbit has 6 darts in, so the graph is bipartite, 6-regular, and has
4M vertices.  Distinct voltages within a pair (i, j) keep it simple.

WHY FOUR SOURCES.  Left multiplication by h in G is an automorphism that is transitive on each orbit.
So diameter <= 5 holds iff the radius-5 balls of the four representatives (0, M, 2M, 3M) cover everything.

NEW HELPER: DENSE COST.  The adjacency matrix A (N x N, float32) is maintained incrementally: changing one
dart only touches M matrix entries.  The four BFS fronts are advanced together as a 4 x N matrix product
R <- min(R + R @ A, 1).  This replaces per-source sparse BFS with a few dense BLAS calls per move.

SEARCH.  Simulated annealing over the voltages with random restarts and random dart patterns.  Candidate
groups are metacyclic Z_m x| Z_k with orders 172..200 (so 4M > 684), plus Heis(3) x Z_7 (order 189).
Every result is checked with lib.is_valid.  If nothing beats the checked 660-vertex Haar fallback, that
fallback is returned.
"""
import math
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def group_heis3():
    """Heisenberg group mod 3 (order 27), element (a, b, c) -> a*9 + b*3 + c, identity 0."""
    p = 3
    e = np.arange(p ** 3, dtype=np.int64)
    A, B, C = e // 9, (e // 3) % 3, e % 3
    Ap = (A[:, None] + A[None, :]) % p
    Bp = (B[:, None] + B[None, :]) % p
    Cp = (C[:, None] + C[None, :] + A[:, None] * B[None, :]) % p
    return _finish(Ap * 9 + Bp * 3 + Cp)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    C = (np.arange(k)[:, None] + np.arange(k)[None, :]) % k
    MT4 = MT0[:, None, :, None] * k + C[None, :, None, :]
    return _finish(MT4.reshape(n0 * k, n0 * k))


# ------------------------------------------------------------------------ two-orbit lift

PATTERNS = [
    [[3, 3], [3, 3]],
    [[2, 4], [4, 2]],
    [[4, 2], [2, 4]],
    [[1, 5], [5, 1]],
    [[5, 1], [1, 5]],
]


def dense_adj(MT, M, volt):
    """Dense float32 adjacency matrix (4M x 4M) of the lift described by volt."""
    N = 4 * M
    A = np.zeros((N, N), dtype=np.float32)
    ar = np.arange(M, dtype=np.int64)
    for (i, j), vs in volt.items():
        for g in vs:
            u = i * M + ar
            v = (2 + j) * M + MT[ar, g]
            A[u, v] = 1.0
            A[v, u] = 1.0
    return A


def set_dart(A, MT, M, pair, g, val):
    """Set (val = 0 or 1) the M edges of dart (i, j, g) in the dense adjacency matrix."""
    i, j = pair
    ar = np.arange(M, dtype=np.int64)
    u = i * M + ar
    v = (2 + j) * M + MT[ar, g]
    A[u, v] = val
    A[v, u] = val


def cost_dense(A, M):
    """Uncovered vertices summed over the four orbit representatives, radius 5.  0 means diameter <= 5.

    The four BFS balls are advanced together: R <- min(R + R @ A, 1), a few dense products in total.
    """
    N = A.shape[0]
    R = np.zeros((4, N), dtype=np.float32)
    R[np.arange(4), [0, M, 2 * M, 3 * M]] = 1.0
    for _ in range(5):
        Rn = np.minimum(R + R @ A, 1.0)
        if np.array_equal(Rn, R):
            break
        R = Rn
    return int(round(4 * N - float(R.sum())))


def to_edges(MT, M, volt):
    ar = np.arange(M, dtype=np.int64)
    E = []
    for (i, j), vs in volt.items():
        for g in vs:
            u = i * M + ar
            v = (2 + j) * M + MT[ar, g]
            E.extend(zip(u.tolist(), v.tolist()))
    return 4 * M, [(int(a), int(b)) for a, b in E]


def search_group(MT, M, deadline, rng, T=2.0, patience=4000):
    """Annealing over voltages with random restarts.  Returns a volt dict with cost 0, or None."""
    while time.monotonic() < deadline:
        pat = PATTERNS[int(rng.integers(len(PATTERNS)))]
        volt = {}
        for i in range(2):
            for j in range(2):
                c = pat[i][j]
                volt[(i, j)] = [int(x) for x in rng.choice(M, c, replace=False)] if c > 0 else []
        A = dense_adj(MT, M, volt)
        cur = cost_dense(A, M)
        pairs = [p for p in volt if volt[p]]
        since = 0
        while since < patience and time.monotonic() < deadline:
            if cur == 0:
                return volt
            p = pairs[int(rng.integers(len(pairs)))]
            k = int(rng.integers(len(volt[p])))
            x = int(rng.integers(M))
            if x in volt[p]:
                since += 1
                continue
            old = volt[p][k]
            set_dart(A, MT, M, p, old, 0.0)
            set_dart(A, MT, M, p, x, 1.0)
            c2 = cost_dense(A, M)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                volt[p][k] = x
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                set_dart(A, MT, M, p, x, 0.0)
                set_dart(A, MT, M, p, old, 1.0)
                since += 1
        if cur == 0:
            return volt
    return None


# ------------------------------------------------------------------------ candidates

def candidates():
    """Non-abelian metacyclic groups of order 172..200 (one lam per (m, k)), plus Heis(3) x Z_7 (189)."""
    out = []
    for n_ in range(172, 201):
        for m in range(3, n_ + 1):
            if n_ % m:
                continue
            k = n_ // m
            if k < 2:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((n_, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
                    break
    out.append((189, lambda: group_times_cyclic(group_heis3(), 7)))
    out.sort(key=lambda t: t[0])
    return out[:16]


# ------------------------------------------------------------------------ fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Valid 660-vertex Haar graph (group_meta(33, 10, 26)), checked before return."""
    MT, _ = group_meta(33, 10, 26)
    N = MT.shape[0]
    edges = []
    for s in FALLBACK_S:
        for g in range(N):
            edges.append((g, N + int(MT[s, g])))
    return 2 * N, edges


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return 2, [(0, 1)]


# ------------------------------------------------------------------------ entry point

TARGET = (6, 5)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates()
    best = None
    for idx, (n_, builder) in enumerate(cands):
        if best is not None and 4 * n_ <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        end = now + rem / (len(cands) - idx)
        try:
            MT, _ = builder()
            M = MT.shape[0]
            volt = search_group(MT, M, end, rng)
            if volt is None:
                continue
            n, edges = to_edges(MT, M, volt)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue
    if best is not None:
        return best
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
