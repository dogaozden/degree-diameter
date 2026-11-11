"""Multi-orbit group lifts for the (d=6, D=5) target, searched with all-source bitset BFS.

CONSTRUCTION.  Pick K orbits per side (K = 2 or 3) and a group G of order M.  A-orbits are i = 0..K-1 with
ids i*M+x, and B-orbits are j = 0..K-1 with ids (K+j)*M+x.  A K x K dart-count matrix C has row sums and
column sums equal to d = 6.  A dart (i, j, g) joins (i, x) to (K+j, x*g) for every x in G.  Distinct voltages
inside each (i, j) keep the graph simple.  The result is bipartite, 6-regular, with 2KM vertices.

NEW HELPER: all-source bitset BFS.  Instead of one BFS per orbit representative, keep a boolean matrix
R of shape (sources, N) and advance every source together with R | R[:, nbr].any(axis=2).  That is one
numpy operation per BFS level.  Covering from the 2K orbit representatives (identity of each orbit) is
exactly the diameter condition, because left multiplication is an automorphism that is transitive on each orbit.

SEARCH.  Simulated annealing over the voltages.  A move rewrites only the M neighbour slots of the changed
dart, in place, and reverts them if rejected.  Random restarts continue until the time slice ends.
Every candidate is checked with lib.is_valid.  If nothing beats the record, a verified 660-vertex Haar
graph is returned.
"""
import math
import time
from math import gcd

import numpy as np

import lib

DEG = 6
DIAM = 5
TARGET = (6, 5)
T_SA = 2.0
PATIENCE = 3000

PAT3 = [
    [[2, 2, 2], [2, 2, 2], [2, 2, 2]],
    [[3, 2, 1], [2, 2, 2], [1, 2, 3]],
    [[2, 3, 1], [3, 1, 2], [1, 2, 3]],
    [[4, 1, 1], [1, 4, 1], [1, 1, 4]],
    [[3, 3, 0], [3, 0, 3], [0, 3, 3]],
]
PAT2 = [
    [[3, 3], [3, 3]],
    [[2, 4], [4, 2]],
    [[4, 2], [2, 4]],
    [[1, 5], [5, 1]],
    [[5, 1], [1, 5]],
]


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with element (a, j) -> a*k + j.  Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def group_for(M):
    """A non-abelian metacyclic group of order M if one exists, else the cyclic group Z_M."""
    for k in range(2, M):
        if M % k:
            continue
        m = M // k
        if m < 3:
            continue
        for lam in range(2, m):
            if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                return group_meta(m, k, lam)
    return group_meta(M, 1, 1)


# ------------------------------------------------------------------------ lift helpers

def offsets(C, K):
    """oa[i][j]: first A-slot of orbit i used by pair (i,j); ob[i][j]: first B-slot of orbit j used by pair (i,j)."""
    oa = [[sum(C[i][:j]) for j in range(K)] for i in range(K)]
    ob = [[sum(C[r][j] for r in range(i)) for j in range(K)] for i in range(K)]
    return oa, ob


def set_slot(nbr, MT, inv, K, M, i, j, sa, sb, g):
    """Write the dart (i, j, g) into A-slot sa of orbit i and B-slot sb of orbit j, for all M lifts."""
    ar = np.arange(M, dtype=np.int64)
    nbr[i * M + ar, sa] = (K + j) * M + MT[ar, g]
    nbr[(K + j) * M + ar, sb] = i * M + MT[ar, inv[g]]


def build_nbr(MT, inv, K, M, C, volt):
    N = 2 * K * M
    nbr = np.empty((N, DEG), dtype=np.int64)
    oa, ob = offsets(C, K)
    for i in range(K):
        for j in range(K):
            for k, g in enumerate(volt[i][j]):
                set_slot(nbr, MT, inv, K, M, i, j, oa[i][j] + k, ob[i][j] + k, g)
    return nbr


def cost(nbr, N, srcs):
    """Uncovered (source, vertex) pairs within radius DIAM, all sources advanced together. 0 means valid."""
    S = len(srcs)
    R = np.zeros((S, N), dtype=bool)
    R[np.arange(S), srcs] = True
    for _ in range(DIAM):
        R2 = R | R[:, nbr].any(axis=2)
        if np.array_equal(R2, R):
            break
        R = R2
    return S * N - int(R.sum())


def to_edges(MT, K, M, volt):
    ar = np.arange(M, dtype=np.int64)
    E = []
    for i in range(K):
        for j in range(K):
            for g in volt[i][j]:
                u = i * M + ar
                v = (K + j) * M + MT[ar, g]
                E.extend(zip(u.tolist(), v.tolist()))
    return 2 * K * M, [(int(a), int(b)) for a, b in E]


# ------------------------------------------------------------------------ search

def search(MT, inv, K, M, deadline, rng):
    """Annealing over voltages with random restarts.  Returns (C, volt) with cost 0, or None."""
    N = 2 * K * M
    srcs = np.array([o * M for o in range(2 * K)], dtype=np.int64)
    pool = PAT3 if K == 3 else PAT2
    while time.monotonic() < deadline:
        C = pool[int(rng.integers(len(pool)))]
        oa, ob = offsets(C, K)
        volt = [[[] for _ in range(K)] for _ in range(K)]
        for i in range(K):
            for j in range(K):
                c = C[i][j]
                if c:
                    volt[i][j] = [int(x) for x in rng.choice(M, c, replace=False)]
        nbr = build_nbr(MT, inv, K, M, C, volt)
        cur = cost(nbr, N, srcs)
        pairs = [(i, j) for i in range(K) for j in range(K) if C[i][j]]
        since = 0
        while since < PATIENCE and time.monotonic() < deadline:
            if cur == 0:
                return C, volt
            i, j = pairs[int(rng.integers(len(pairs)))]
            k = int(rng.integers(len(volt[i][j])))
            x = int(rng.integers(M))
            if x in volt[i][j]:
                since += 1
                continue
            old = volt[i][j][k]
            sa, sb = oa[i][j] + k, ob[i][j] + k
            set_slot(nbr, MT, inv, K, M, i, j, sa, sb, x)
            c2 = cost(nbr, N, srcs)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T_SA):
                volt[i][j][k] = x
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                set_slot(nbr, MT, inv, K, M, i, j, sa, sb, old)
                since += 1
        if cur == 0:
            return C, volt
    return None


# ------------------------------------------------------------------------ candidates

def configs():
    """Configurations with more than 684 vertices, smallest first (cheapest to search)."""
    out = []
    for M in range(115, 127):
        out.append((6 * M, 3, M))
    for M in range(172, 186):
        out.append((4 * M, 2, M))
    out = [c for c in out if c[0] > 684]
    out.sort()
    return out[:14]


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

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cfgs = configs()
    best = None
    for idx, (nv, K, M) in enumerate(cfgs):
        if best is not None and nv <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        end = now + rem / (len(cfgs) - idx)
        try:
            MT, inv = group_for(M)
            found = search(MT, inv, K, M, end, rng)
            if found is None:
                continue
            C, volt = found
            n, edges = to_edges(MT, K, M, volt)
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
