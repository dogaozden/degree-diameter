import math
import random
import time

import numpy as np

import lib

# Iterations per annealing attempt.
ITERS = 1500


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3, calibration).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q > 40:
            continue
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Groups: semidirect products Z_m x|_r Z_k, element (a, b) coded as a*k + b.
# Identity is index 0.
# ----------------------------------------------------------------------------

def _semidirect_mul_table(m, k2, r):
    """M[x, g] = x * g for Z_m x|_r Z_k2 (requires r^k2 = 1 mod m)."""
    G = m * k2
    idx = np.arange(G, dtype=np.int64)
    A = idx // k2
    B = idx % k2
    powr = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
    a1 = A[:, None]
    b1 = B[:, None]
    a2 = A[None, :]
    b2 = B[None, :]
    return ((a1 + powr[b1] * a2) % m) * k2 + (b1 + b2) % k2


def _perm_tables(M):
    """PM[g, x] = x*g (right multiplication permutations) and QM = their inverses."""
    G = M.shape[0]
    PM = np.ascontiguousarray(M.T)
    QM = np.empty_like(PM)
    rows = np.arange(G)[:, None]
    QM[rows, PM] = np.arange(G)[None, :]
    return PM, QM


def _group_options(G, rng):
    """Semidirect descriptions (m, k2, r) of a group of order G (cyclic included)."""
    opts = []
    for k2 in range(1, min(G, 60) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        opts.append((m, k2, 1))
        if k2 > 1:
            rs = [r for r in range(2, m)
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if rs:
                for r in rng.sample(rs, min(len(rs), 2)):
                    opts.append((m, k2, r))
    return opts


# ----------------------------------------------------------------------------
# Multi-orbit voltage lift search (new routine).
#
# Base graph: k A-orbits and k B-orbits, each of size G. There are d*k darts.
# Dart t = (At[t], Bt[t], g_t) joins (A, x) to (B, x * g_t) for all x in G.
# A-orbits and B-orbits each receive exactly d darts, so the lift is d-regular
# with n = 2kG vertices and is bipartite by construction.
#
# Diameter check: left multiplication is an automorphism of the lift, so it
# suffices to BFS from the identity of each of the 2k base orbits. All 2k
# sources are advanced together as one batched boolean array. The cost is the
# number of (source, vertex) pairs not reached within D steps.
# ----------------------------------------------------------------------------

def _cost(k, G, D, At, Bt, Gt, PM, QM, MA):
    T = At.shape[0]
    S = 2 * k
    n = 2 * k * G
    MB = (np.arange(k)[:, None] == Bt[None, :]).astype(np.float32)
    Pt = PM[Gt]
    Qt = QM[Gt]
    Pb = np.broadcast_to(Pt, (S, T, G))
    Qb = np.broadcast_to(Qt, (S, T, G))
    FA = np.zeros((S, k, G), dtype=bool)
    FB = np.zeros((S, k, G), dtype=bool)
    ar = np.arange(k)
    FA[ar, ar, 0] = True          # source s < k : A-orbit s, identity
    FB[ar + k, ar, 0] = True      # source s = k + j : B-orbit j, identity
    VA = FA.copy()
    VB = FB.copy()
    for _ in range(D):
        C = np.take_along_axis(FA[:, At, :], Qb, axis=2).astype(np.float32)
        NB = np.matmul(MB, C) > 0.5
        Dd = np.take_along_axis(FB[:, Bt, :], Pb, axis=2).astype(np.float32)
        NA = np.matmul(MA, Dd) > 0.5
        NB &= ~VB
        NA &= ~VA
        VB |= NB
        VA |= NA
        FA, FB = NA, NB
        if not FA.any() and not FB.any():
            break
    return S * n - int(VA.sum()) - int(VB.sum())


def _anneal(k, d, G, D, rng, PM, QM, deadline, iters):
    """Anneal voltages and B-assignment of a d-regular k-orbit lift. Returns (At, Bt, Gt) or None."""
    T = k * d
    At = np.repeat(np.arange(k, dtype=np.int64), d)
    bl = [j for j in range(k) for _ in range(d)]
    rng.shuffle(bl)
    Bt = np.array(bl, dtype=np.int64)
    Gt = np.array([rng.randrange(G) for _ in range(T)], dtype=np.int64)
    MA = (np.arange(k)[:, None] == At[None, :]).astype(np.float32)
    cost = _cost(k, G, D, At, Bt, Gt, PM, QM, MA)
    T0, T1 = 3.0, 0.3
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (T1 / T0) ** (it / iters)
        t = rng.randrange(T)
        if k > 1 and rng.random() < 0.3:
            t2 = rng.randrange(T)
            if Bt[t] == Bt[t2]:
                continue
            Bt[t], Bt[t2] = Bt[t2], Bt[t]
            c2 = _cost(k, G, D, At, Bt, Gt, PM, QM, MA)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                Bt[t], Bt[t2] = Bt[t2], Bt[t]
        else:
            old = int(Gt[t])
            Gt[t] = rng.randrange(G)
            c2 = _cost(k, G, D, At, Bt, Gt, PM, QM, MA)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                Gt[t] = old
    if cost == 0:
        return At, Bt, Gt
    return None


def _edges(k, G, At, Bt, Gt, M):
    """Expand the base darts into the lift's edge list (deduplicated)."""
    xs = np.arange(G, dtype=np.int64)
    seen = set()
    for t in range(len(At)):
        i = int(At[t])
        j = k + int(Bt[t])
        g = int(Gt[t])
        a = (i * G + xs).tolist()
        b = (j * G + M[:, g]).tolist()
        seen.update(zip(a, b))
    return sorted(seen)


def _probe(n, d, D, slice_end, rng):
    """Try to build a valid d-regular bipartite graph on exactly n vertices (n = 2kG)."""
    n2 = n // 2
    configs = []
    for k in (1, 2, 3, 4, 5, 6, 7, 8):
        if n2 % k:
            continue
        G = n2 // k
        if G < 3:
            continue
        for opt in _group_options(G, rng):
            configs.append((k, G, opt))
    if not configs:
        return None
    rng.shuffle(configs)
    i = 0
    while time.monotonic() < slice_end:
        k, G, (m, k2, r) = configs[i % len(configs)]
        i += 1
        M = _semidirect_mul_table(m, k2, r)
        PM, QM = _perm_tables(M)
        res = _anneal(k, d, G, D, rng, PM, QM, slice_end, ITERS)
        if res is None:
            continue
        At, Bt, Gt = res
        edges = _edges(k, G, At, Bt, Gt, M)
        nn = 2 * k * G
        if lib.is_valid(nn, edges, d, D):
            return nn, edges
    return None


# ----------------------------------------------------------------------------
# Entry point. Binary search over the vertex count n: each probe runs the
# multi-orbit lift search with a time slice.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            return pg

    target = (d == 7 and D == 5)
    lo = best[0]
    if target:
        hi = 1160
        first = 1000
    else:
        hi = min(lib._moore_bound(d, D), 3000)
        first = None
    if hi <= lo:
        return best

    probe_n = first
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0 or hi - lo <= 2:
            break
        if probe_n is None:
            probe_n = ((lo + hi) // 2) // 2 * 2
        if not (lo < probe_n < hi):
            break
        slice_end = now + min(remaining, max(2.0, remaining * 0.35))
        res = _probe(probe_n, d, D, slice_end, rng)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res
            lo = res[0]
        else:
            hi = probe_n
        probe_n = None

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
