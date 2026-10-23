"""Two-orbit group lifts for the (d=6, D=5) target, with a dense frontier cost and a wider order sweep.

CONSTRUCTION.  Take a group G of order M and four vertex orbits: A-orbits 0 and 1, B-orbits 2 and 3.
Vertex (o, x) has id o*M + x.  A dart (i, j, g) joins (i, x) to (2+j, x*g) for all x in G.  Each A-orbit
has 6 darts out and each B-orbit has 6 darts in, so the graph is bipartite, 6-regular, with 4M vertices.
Left multiplication by G is an automorphism, so diameter <= 5 holds iff the radius-5 balls of the four
orbit representatives cover all 4M vertices.

NEW HELPER (dense frontier cost).  The four BFS sources are propagated together as a 4 x N 0/1 matrix R.
Each step is R <- (R @ (I + A)) > 0, so five matrix products give the radius-5 balls.  This replaces the
per-source Python BFS and is much faster inside the annealing loop.

NEW SWEEP.  Orders 171..200 are tried in ascending order, first with one metacyclic group per order and then
with the remaining groups, so runs can reach orders above the record 171 (4M = 684).  Every result is checked
with lib.is_valid.  If no candidate is valid, a checked 660-vertex Haar graph is returned.
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


def build_adj(MT, M, volt):
    """Dense symmetric 0/1 adjacency (4M x 4M) of the lift.  No collisions: darts in one pair are distinct."""
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


def dense_cost(A, M):
    """Uncovered vertices summed over the four orbit representatives, radius 5.  0 means diameter <= 5.

    All four BFS sources advance together as rows of R; each step is one matrix product.
    """
    N = A.shape[0]
    B = A.copy()
    np.fill_diagonal(B, 1.0)
    R = np.zeros((4, N), dtype=np.float32)
    R[np.arange(4), [0, M, 2 * M, 3 * M]] = 1.0
    for _ in range(5):
        R = ((R @ B) > 0).astype(np.float32)
    return int(4 * N - R.sum())


def to_edges(MT, M, volt):
    ar = np.arange(M, dtype=np.int64)
    E = []
    for (i, j), vs in volt.items():
        for g in vs:
            u = i * M + ar
            v = (2 + j) * M + MT[ar, g]
            E.extend(zip(u.tolist(), v.tolist()))
    return 4 * M, [(int(a), int(b)) for a, b in E]


def anneal(MT, M, deadline, rng, patience=3000):
    """Simulated annealing over voltages with random restarts.  Returns a volt dict with cost 0, or None."""
    pair_keys = [(i, j) for i in range(2) for j in range(2)]
    while time.monotonic() < deadline:
        pat = PATTERNS[int(rng.integers(len(PATTERNS)))]
        volt = {}
        for i in range(2):
            for j in range(2):
                c = pat[i][j]
                volt[(i, j)] = [int(x) for x in rng.choice(M, c, replace=False)] if c > 0 else []
        cur = dense_cost(build_adj(MT, M, volt), M)
        pairs = [p for p in pair_keys if volt[p]]
        since = 0
        T = 1.5
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
            volt[p][k] = x
            c2 = dense_cost(build_adj(MT, M, volt), M)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                volt[p][k] = old
                since += 1
        if cur == 0:
            return volt
    return None


# ------------------------------------------------------------------------ candidates

def candidates():
    """Pass-1 list (one group per order 171..200, ascending) followed by pass-2 (other groups)."""
    first, second = [], []
    for M in range(171, 201):
        gs = []
        for m in range(3, M):
            if M % m:
                continue
            k = M // m
            if k < 2:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    gs.append((m, k, lam))
                    break
        if gs:
            m, k, lam = gs[0]
            first.append((M, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
            for m, k, lam in gs[1:3]:
                second.append((M, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
        if M == 189:
            second.append((189, lambda: group_times_cyclic(group_heis3(), 7)))
    return first + second


def to_check_order(cands):
    return cands


# ------------------------------------------------------------------------ fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Valid 660-vertex Haar graph (group_meta(33, 10, 26))."""
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
    budget = max(1.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = to_check_order(candidates())
    best = None
    for idx, (M, builder) in enumerate(cands):
        if best is not None and 4 * M <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.3:
            break
        end = now + rem / (len(cands) - idx)
        try:
            MT, _ = builder()
            Mg = MT.shape[0]
            volt = anneal(MT, Mg, end, rng)
            if volt is None:
                continue
            n, edges = to_edges(MT, Mg, volt)
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
