"""Bold change for d=6, D=5: voltage lifts of K_{t,t} over small groups, found by annealing.

Instead of a single-orbit Haar graph (t=1 in the usual form), each graph here has t A-orbits and t B-orbits.
Vertices are (g, A_i) and (g, B_j) for g in a group G of order N, with edges (g, A_i) ~ (s*g, B_j) for each voltage
s in a block V[i][j] of size n = 6/t.  Every vertex has degree 6 and the graph is bipartite with 2tN vertices.
Right multiplication by any h in G is an automorphism, so the diameter is at most 5 iff every base vertex
(e, A_i) and (e, B_j) reaches every vertex within 5 steps.  The cost is the number of (base vertex, vertex)
pairs at distance more than 5, and cost 0 means valid.

Each step changes one voltage, updates only the two adjacency columns it affects, and recomputes the BFS cost
with numpy bitsets.  Every returned graph is checked with lib.is_valid.  If no lift succeeds in time, the
previously verified 660-vertex Haar graph is returned.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6
DIAM = 5
PATIENCE = 4000
TEMP = 1.2
NEED = 685  # smallest vertex count that beats the record 684


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int64)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def group_specs(N):
    """Semidirect-product parameters (m, k, lam) of order N; non-abelian ones first, cyclic/abelian last."""
    nonab, ab = [], []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        ab.append((m, k, 1))
        if k == 1:
            continue
        lams = [l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1 % m]
        nonab += [(m, k, l) for l in lams[:2]]
    return nonab + ab


def candidate_groups(N_lo, N_hi, cap):
    specs = []
    for N in range(N_lo, N_hi + 1):
        specs += group_specs(N)
    # remove duplicates while keeping order
    seen, out = set(), []
    for s in specs:
        if s not in seen:
            seen.add(s)
            out.append(s)
    return out[:cap]


# ------------------------------------------------------------------------- lift graph

def set_slot(adj, t, n, N, g, i, j, k, s, MT, inv):
    """Write voltage s into block (i, j), position k, updating the two affected adjacency columns."""
    adj[i * N:(i + 1) * N, j * n + k] = (t + j) * N + MT[s, g]
    adj[(t + j) * N:(t + j + 1) * N, i * n + k] = i * N + MT[inv[s], g]


def lift_cost(adj, src, V):
    """Number of (source, vertex) pairs at distance more than DIAM."""
    c = len(src)
    R = np.zeros((V, c), dtype=bool)
    R[src, np.arange(c)] = True
    for _ in range(DIAM):
        R = R | R[adj].any(axis=1)
    return V * c - int(R.sum())


def full_adj(Vv, t, n, N, MT, inv):
    adj = np.empty((2 * t * N, DEG), dtype=np.intp)
    g = np.arange(N)
    for i in range(t):
        for j in range(t):
            for k in range(n):
                set_slot(adj, t, n, N, g, i, j, k, int(Vv[i, j, k]), MT, inv)
    return adj


def anneal(t, n, MT, inv, N, deadline, rng):
    """Anneal the voltages of a t x t lift.  Returns (best voltages, best cost)."""
    V = 2 * t * N
    src = np.arange(2 * t) * N
    g = np.arange(N)
    adj = np.empty((V, DEG), dtype=np.intp)

    def init():
        Vv = np.empty((t, t, n), dtype=np.int64)
        for i in range(t):
            for j in range(t):
                Vv[i, j] = rng.choice(N, n, replace=False)
        for i in range(t):
            for j in range(t):
                for k in range(n):
                    set_slot(adj, t, n, N, g, i, j, k, int(Vv[i, j, k]), MT, inv)
        return Vv

    Vv = init()
    cur = lift_cost(adj, src, V)
    best, bestc = Vv.copy(), cur
    since = 0
    while cur > 0 and time.monotonic() < deadline:
        i = int(rng.integers(t))
        j = int(rng.integers(t))
        k = int(rng.integers(n))
        x = int(rng.integers(N))
        if x in Vv[i, j]:
            continue
        old = int(Vv[i, j, k])
        Vv[i, j, k] = x
        set_slot(adj, t, n, N, g, i, j, k, x, MT, inv)
        c = lift_cost(adj, src, V)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            cur = c
            if cur < bestc:
                best, bestc, since = Vv.copy(), cur, 0
        else:
            Vv[i, j, k] = old
            set_slot(adj, t, n, N, g, i, j, k, old, MT, inv)
        since += 1
        if since > PATIENCE:
            Vv = init()
            cur = lift_cost(adj, src, V)
            since = 0
    return best, bestc


def lift_edges(Vv, t, n, N, MT, inv):
    adj = full_adj(Vv, t, n, N, MT, inv)
    edges = [(u, int(v)) for u in range(t * N) for v in adj[u]]
    return 2 * t * N, edges


# ---------------------------------------------------------------- Haar fallback

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked_haar(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def fallback_graph():
    """Verified 660-vertex Haar graph for d=6, D=5."""
    try:
        MT, _ = group_meta(33, 10, 26)
        return checked_haar(MT, [0, 179, 116, 180, 47, 306], 6, 5)
    except Exception:
        return None


# ------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)

    best_valid = fallback_graph()

    # (lift size t, share of the budget).  Block size n = 6 / t; vertex count is 2 * t * N.
    plan = [(6, 0.5), (3, 0.3), (2, 0.2)]
    for t, share in plan:
        n = 6 // t
        N_min = -(-NEED // (2 * t))
        groups = candidate_groups(N_min, N_min + 2, cap=8)
        if not groups:
            continue
        section_end = time.monotonic() + share * (deadline_all - time.monotonic())
        for idx, (m, k, lam) in enumerate(groups):
            now = time.monotonic()
            if now >= deadline_all:
                break
            slice_end = now + (section_end - now) / (len(groups) - idx)
            try:
                MT, inv = group_meta(m, k, lam)
                N = m * k
                if 2 * t * N < NEED or 2 * t * N > lib.moore_bound(DEG, DIAM):
                    continue
                Vv, c = anneal(t, n, MT, inv, N, slice_end, rng)
                if c == 0:
                    nv, edges = lift_edges(Vv, t, n, N, MT, inv)
                    if lib.is_valid(nv, edges, DEG, DIAM) and (best_valid is None or nv > best_valid[0]):
                        return nv, edges
            except Exception:
                continue

    if best_valid is not None:
        return best_valid
    return trivial(d, D)
