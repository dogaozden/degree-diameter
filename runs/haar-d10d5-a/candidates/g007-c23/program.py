"""Bi-Cayley lift search for the bipartite degree-diameter problem (d=10, D=5), with a Haar fallback.

CONSTRUCTION.  Let G be a finite group of order N and let the base graph have P = 2 vertices on each side,
A_0, A_1 and B_0, B_1, with dart multiplicities m_ij (row and column sums equal to d).  A dart (i, j, g) joins
(A_i, x) to (B_j, x*g) for every x in G.  The lift has 4N vertices and is d-regular and bipartite.

Left multiplication by h in G is an automorphism, so G acts transitively on each fibre.  Hence the diameter is at
most D iff every base vertex, taken at the identity, reaches all 4N vertices within D steps.  Each check is a
vectorised BFS from 4 representatives, so a cost evaluation is cheap.  The cost is the number of unreached
(representative, vertex) pairs.  Simulated annealing over the dart voltages, with distinct voltages inside each
pair, drives the cost to 0.  Non-abelian metacyclic groups Z_m x| Z_k of order N in [900, 1100] are used, so a
valid lift with N >= 896 already beats the old 3582-vertex fallback and N >= 1001 beats the record 4000.

SAFETY.  Every returned graph passes lib.is_valid.  If no lift succeeds, the validated Haar graph of order 3582 is
returned.  Other (d, D) cases get a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
P = 2                       # base vertices per side
N_LO, N_HI = 900, 1100      # candidate group orders
SLICE = 6.0                 # seconds of annealing per (group, restart)
STALL = 3000                # steps without improvement before restarting
TEMP = 2.0
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
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


# ----------------------------------------------------------------------------------- lift construction

def _lift(MT, inv, darts, N, d):
    """Neighbour array (4N, d).  A_i vertex x is i*N + x, B_j vertex y is (P+j)*N + y.
    Dart (i, j, g): A-side x ~ B-side x*g, so the B-side neighbour of y is x = y*g^-1."""
    xs = np.arange(N)
    nbr = np.empty((2 * P * N, d), dtype=np.int64)
    ca = [0] * P
    cb = [0] * P
    for i, j, g in darts:
        sa = ca[i]
        ca[i] += 1
        nbr[i * N:(i + 1) * N, sa] = (P + j) * N + MT[xs, g]
        sb = cb[j]
        cb[j] += 1
        nbr[(P + j) * N:(P + j + 1) * N, sb] = i * N + MT[xs, inv[g]]
    return nbr


def _bfs_cost(nbr, N, D):
    """Number of (representative, vertex) pairs at distance > D.  Representatives: identity in each fibre."""
    n = nbr.shape[0]
    total = 0
    for r in range(0, n, N):
        seen = np.zeros(n, dtype=bool)
        seen[r] = True
        front = np.array([r], dtype=np.int64)
        for _ in range(D):
            nb = nbr[front].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            front = nb
        total += n - int(seen.sum())
    return total


def _edges(nbr, N, d):
    """Edge list: every A-side vertex with its d neighbours (each edge appears once)."""
    u = np.repeat(np.arange(P * N, dtype=np.int64), d)
    v = nbr[:P * N].ravel()
    return list(zip(u.tolist(), v.tolist()))


def _anneal(MT, inv, N, d, mult, D, end, rng):
    """Anneal dart voltages until the lift has diameter <= D.  Returns the darts, or None if out of time or stalled."""
    darts = []
    used = {}
    for (i, j), mm in mult.items():
        gs = [int(x) for x in rng.choice(N, mm, replace=False)]
        used[(i, j)] = set(gs)
        darts.extend([[i, j, g] for g in gs])
    cur = _bfs_cost(_lift(MT, inv, darts, N, d), N, D)
    best_c = cur
    stall = 0
    while True:
        if cur == 0:
            return darts
        if time.monotonic() >= end or stall > STALL:
            return None
        t = int(rng.integers(len(darts)))
        i, j, g = darts[t]
        ss = used[(i, j)]
        ng = int(rng.integers(N))
        while ng in ss:
            ng = int(rng.integers(N))
        darts[t][2] = ng
        c = _bfs_cost(_lift(MT, inv, darts, N, d), N, D)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            ss.discard(g)
            ss.add(ng)
            cur = c
            if c < best_c:
                best_c = c
                stall = 0
            else:
                stall += 1
        else:
            darts[t][2] = g
            stall += 1


def _meta_candidates(rng):
    """Non-abelian metacyclic groups Z_m x| Z_kz with order N in [N_LO, N_HI], up to two per order, shuffled."""
    cands = []
    for N in range(N_LO, N_HI + 1):
        opts = []
        for kz in range(2, N):
            if N % kz:
                continue
            m = N // kz
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, kz, m) == 1:
                    opts.append((m, kz, lam))
        if opts:
            pick = rng.choice(len(opts), min(2, len(opts)), replace=False)
            for t in pick:
                m, kz, lam = opts[int(t)]
                cands.append((N, m, kz, lam))
    order = rng.permutation(len(cands))
    return [cands[int(t)] for t in order]


def _search(d, D, seed, time_limit):
    """Round-robin annealing over candidate groups.  Returns the best validated (n, edges), or None."""
    t0 = time.monotonic()
    deadline = t0 + min(0.8 * time_limit, time_limit - 8.0)
    rng = np.random.default_rng(seed)
    cands = _meta_candidates(rng)
    best = None
    best_N = 0
    while True:
        left = [c for c in cands if c[0] > best_N]
        if not left or time.monotonic() >= deadline:
            break
        for N, m, kz, lam in left:
            now = time.monotonic()
            if now >= deadline:
                break
            if N <= best_N:
                continue
            end = min(deadline, now + SLICE)
            MT, inv = group_meta(m, kz, lam)
            k1 = int(rng.integers(1, d))
            mult = {(0, 0): k1, (0, 1): d - k1, (1, 0): d - k1, (1, 1): k1}
            darts = _anneal(MT, inv, N, d, mult, D, end, rng)
            if darts is None:
                continue
            nbr = _lift(MT, inv, darts, N, d)
            n = 2 * P * N
            edges = _edges(nbr, N, d)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
    return best


# --------------------------------------------------------------------------------- fallback and checks

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


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        res = _search(d, D, seed, time_limit)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        MT, _ = group_meta(*FALLBACK_GROUP)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
