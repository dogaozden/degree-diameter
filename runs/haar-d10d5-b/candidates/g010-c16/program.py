"""Bold variant for d=10, D=5: 2-orbit bipartite lifts over metacyclic groups.

Construction: 2 A-orbits and 2 B-orbits, each a copy of a group G of order Ng. Each A-orbit and each
B-orbit has 10 darts, 5 to each B-orbit / A-orbit. A dart (i, j, g) joins (A_i, x) to (B_j, x*g).
The lift is a simple 10-regular bipartite graph on 4*Ng vertices. Left multiplication by G is an
automorphism, so the diameter is at most 5 iff a BFS from the four orbit representatives reaches all
vertices within 5 steps. Voltages are annealed to make that cost zero.

Ladder: try increasing group orders (4*Ng must exceed the fallback's 3582 and then the record 4000).
Every returned graph is checked with lib.is_valid. The checked Haar fallback (3582 vertices) is
returned if no lift succeeds. Other (d, D) cases get the trivial always-valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
K = 2                    # orbits per side
DEG = 10                 # degree of the lift
DIAM = 5
SLOTS_PER_CLASS = 5      # darts per (A_i, B_j) orbit pair; each orbit sums to K*5 = 10
NCLASS = K * K
NDART = NCLASS * SLOTS_PER_CLASS   # 20 voltages


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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


def find_group(N):
    """Return (m, k, lam) with m*k = N giving a non-abelian metacyclic group if one exists, else the cyclic group."""
    ks = [k for k in range(3, N) if N % k == 0 and N // k >= 3]
    for exact in (True, False):
        for k in ks:
            m = N // k
            for r in range(2, m):
                if math.gcd(r, m) != 1 or r == 1 or pow(r, k, m) != 1:
                    continue
                order = next(e for e in range(1, k + 1) if pow(r, e, m) == 1)
                if order == k or not exact:
                    return m, k, r
    return N, 1, 1


# ------------------------------------------------------------------------- lift construction

def make_nbr(V, MT, inv, Ng):
    """Neighbour table (4*Ng, DEG). A-orbit i occupies rows i*Ng.., B-orbit j occupies rows (K+j)*Ng.."""
    nbr = np.empty((2 * K * Ng, DEG), dtype=np.int64)
    for i in range(K):
        for col in range(DEG):
            j = col // SLOTS_PER_CLASS
            t = i * DEG + col
            nbr[i * Ng:(i + 1) * Ng, col] = (K + j) * Ng + MT[:, V[t]]
    for j in range(K):
        for col in range(DEG):
            i = col // SLOTS_PER_CLASS
            c = col % SLOTS_PER_CLASS
            t = (i * K + j) * SLOTS_PER_CLASS + c
            nbr[(K + j) * Ng:(K + j + 1) * Ng, col] = i * Ng + MT[:, inv[V[t]]]
    return nbr


def lift_cost(nbr, Ng):
    """Number of (orbit representative, vertex) pairs at distance > DIAM. Zero means diameter <= DIAM."""
    N = nbr.shape[0]
    total = 0
    for s in range(2 * K):
        src = s * Ng
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            new = np.zeros(N, dtype=bool)
            new[nbr[front].ravel()] = True
            new &= ~seen
            if not new.any():
                break
            seen |= new
            front = np.flatnonzero(new)
        total += N - int(seen.sum())
    return total


def lift_edges(nbr, Ng):
    """Edge list of the lift; A-rows each contribute DEG edges, so every edge appears once."""
    half = K * Ng
    A = np.repeat(np.arange(half, dtype=np.int64), DEG)
    B = nbr[:half].ravel()
    return 2 * half, list(zip(A.tolist(), B.tolist()))


def anneal(MT, inv, Ng, deadline, rng):
    """Anneal voltages with single-dart moves. Returns (V, cost); cost 0 means a valid lift."""
    V = np.empty(NDART, dtype=np.int64)
    for c in range(NCLASS):
        V[c * SLOTS_PER_CLASS:(c + 1) * SLOTS_PER_CLASS] = rng.choice(Ng, SLOTS_PER_CLASS, replace=False)
    cur = lift_cost(make_nbr(V, MT, inv, Ng), Ng)
    step = 0
    period = 4000
    while cur > 0 and time.monotonic() < deadline:
        step += 1
        frac = (step % period) / period
        base_T = 0.2 + 2.0 * (1.0 - frac) ** 2
        t = int(rng.integers(NDART))
        cls = t // SLOTS_PER_CLASS
        v = int(rng.integers(Ng))
        if v in V[cls * SLOTS_PER_CLASS:(cls + 1) * SLOTS_PER_CLASS]:
            continue   # keep the darts of each orbit pair distinct, so the graph stays simple
        W = V.copy()
        W[t] = v
        c = lift_cost(make_nbr(W, MT, inv, Ng), Ng)
        delta = c - cur
        T = base_T * (1.0 + cur / 100.0)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            V, cur = W, c
    return V, cur


# ---------------------------------------------------------------- Haar fallback and helpers

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# Valid Haar graph of order 3582 (group Z_199 x| Z_9), used when no lift succeeds.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])

# (group order N = 4*Ng / 4 ... i.e. Ng, share of time). Ascending: small wins first, then records.
PLAN = [(900, 1.0), (1000, 1.0), (1010, 2.0), (1020, 2.0), (1040, 1.5)]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end_all = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None
    if best is None:
        best = trivial(d, D)
    best_n = best[0]

    total_w = sum(w for _, w in PLAN)
    for N, w in PLAN:
        now = time.monotonic()
        if now >= end_all:
            break
        slice_end = now + (end_all - now) * w / total_w
        total_w -= w
        try:
            m, k, lam = find_group(N)
            MT, inv = group_meta(m, k, lam)
            Ng = m * k
            V, cur = anneal(MT, inv, Ng, slice_end, rng)
        except Exception:
            continue
        if cur == 0:
            try:
                nbr = make_nbr(V, MT, inv, Ng)
                n, edges = lift_edges(nbr, Ng)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best, best_n = (n, edges), n
            except Exception:
                pass
    return best
