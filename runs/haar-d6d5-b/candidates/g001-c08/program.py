"""Bold variant for d=6, D=5: a 2x2 group voltage lift instead of a Haar graph.

Construction: a group G of order N (metacyclic Z_m x| Z_k, or cyclic) with four vertex classes
A_0, A_1, B_0, B_1 (each a copy of G), so the graph has 4N vertices. A dart (i, j, g) joins
(i, x) to (j, x*g) for every x in G. Each A_i gets 6 darts and each B_j gets 6 darts, so the
graph is bipartite and 6-regular. Voltages are annealed directly on the number of vertex pairs
at distance > 5, with no Haar-specific cost formula. The validated parent Haar graph (660
vertices) is kept as the fallback, so every return is a checked valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DIAM = 5
DEG = 6
SLICE = 2.5                      # seconds of annealing per group
MATS = [((3, 3), (3, 3)), ((4, 2), (2, 4)), ((5, 1), (1, 5))]   # 2x2 dart multiplicities, row and column sums 6
FALLBACK_S = [0, 179, 116, 180, 47, 306]   # parent's valid Haar graph on group_meta(33, 10, 26)


# ----------------------------------------------------------------------------- groups

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l).  Returns (MT, inv)."""
    if pow(lam, k, m) != 1 % m:
        raise ValueError("need lam^k = 1 mod m")
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def groups_of_order(N):
    """Candidate (m, k, lam) with m*k = N: non-abelian metacyclic groups first, then the cyclic group."""
    res = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                res.append((m, k, lam))
    res = res[:6]
    res.append((N, 1, 1))
    return res


# ------------------------------------------------------------------------ the lift

def build_nb(MT, inv, darts):
    """Neighbour array (4N x DEG).  A_i vertex (i, x) = i*N + x, B_j vertex (j, y) = 2N + j*N + y."""
    N = MT.shape[0]
    n = 4 * N
    nb = np.zeros((n, DEG), dtype=np.int64)
    cA = [0, 0]
    cB = [0, 0]
    xs = np.arange(N)
    for i, j, g in darts:
        nb[i * N:(i + 1) * N, cA[i]] = 2 * N + j * N + MT[xs, g]
        cA[i] += 1
        nb[2 * N + j * N: 2 * N + (j + 1) * N, cB[j]] = i * N + MT[xs, inv[g]]
        cB[j] += 1
    return nb


def bad_count(nb):
    """Number of unordered vertex pairs at distance > DIAM (unreachable pairs included)."""
    n = nb.shape[0]
    reach = np.eye(n, dtype=bool)
    for _ in range(DIAM):
        reach = reach | reach[nb].any(axis=1)
        if reach.all():
            break
    return (n * n - int(reach.sum())) // 2


def random_darts(N, M, rng):
    darts = []
    for i in range(2):
        for j in range(2):
            for g in rng.choice(N, M[i][j], replace=False):
                darts.append((i, j, int(g)))
    return darts


def anneal(MT, inv, rng, deadline):
    """Anneal dart voltages until the lift has diameter <= DIAM.  Returns darts, or None at the deadline."""
    N = MT.shape[0]
    M = MATS[int(rng.integers(len(MATS)))]
    darts = random_darts(N, M, rng)
    cur = bad_count(build_nb(MT, inv, darts))
    best, stall, T = cur, 0, 2.0
    while time.monotonic() < deadline:
        if cur == 0:
            return darts
        k = int(rng.integers(len(darts)))
        i, j, _ = darts[k]
        used = {gg for (ii, jj, gg) in darts if ii == i and jj == j}
        ng = int(rng.integers(N))
        if ng in used:
            continue
        new = list(darts)
        new[k] = (i, j, ng)
        c = bad_count(build_nb(MT, inv, new))
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            darts, cur = new, c
        if cur < best:
            best, stall = cur, 0
        else:
            stall += 1
        if stall > 3000:          # restart from a fresh random lift
            M = MATS[int(rng.integers(len(MATS)))]
            darts = random_darts(N, M, rng)
            cur = bad_count(build_nb(MT, inv, darts))
            best, stall = cur, 0
    return None


# ------------------------------------------------------------------ helpers

def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# -------------------------------------------------------------------- entry

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    deadline = time.monotonic() + 0.8 * time_limit

    # Safe baseline: the parent's validated Haar graph.
    best = None
    try:
        MT0, _ = group_meta(33, 10, 26)
        n0, e0 = haar_edges(MT0, FALLBACK_S)
        if lib.is_valid(n0, e0, d, D):
            best = (n0, e0)
    except Exception:
        best = None
    if best is None:
        best = trivial(d, D)

    rng = np.random.default_rng(seed)
    for N in range(166, 200):
        if time.monotonic() >= deadline:
            break
        if 4 * N <= best[0]:
            continue
        for m, k, lam in groups_of_order(N):
            now = time.monotonic()
            if now >= deadline:
                break
            try:
                MT, inv = group_meta(m, k, lam)
            except Exception:
                continue
            end = min(deadline, now + SLICE)
            try:
                darts = anneal(MT, inv, rng, end)
            except Exception:
                darts = None
            if darts is None:
                continue
            nb = build_nb(MT, inv, darts)
            n = nb.shape[0]
            edges = [(a, int(b)) for a in range(n // 2) for b in nb[a]]
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                break   # move on to larger orders
    return best
