import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baselines: Araujo-Pardo--López record family, projective plane incidence,
# and K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: multi-orbit voltage lifts with a cheap diameter oracle.
#
# Take a group G of order N and m orbits on each side: A_0..A_{m-1} and
# B_0..B_{m-1}, each a copy of G. For each block (i, j) choose a set D_ij of
# c_ij group elements, where the counts form a circulant m x m matrix with
# every row and column summing to d. Edge set:
#     a_{i,x} ~ b_{j, x*g}   for g in D_ij, x in G.
# This is d-regular, bipartite, and has order 2*m*N. Let T = m*N, so the
# order is 2T.
#
# Diameter 3 check: the graph is invariant under left translation by G, so
# every pair is covered by the 2m representatives (A_i, e) and (B_j, e).
# Their distance-<=3 balls are rows of (I+A)^3, which is cheap to compute
# with numpy. The annealing cost is the number of (representative, vertex)
# pairs at distance > 3, and the search can drive it to 0.
#
# Same-side pairs need T - 1 <= d(d-1), so 2T <= 2(d^2-d+1) (the Moore bound).
# The family can exceed single-orbit (m = 1) bi-Cayley graphs because it has
# more freedom in the darts.
# ----------------------------------------------------------------------------

def _specs(N, rng, cap=6):
    """Candidate groups of order N: cyclic plus a sample of semidirect products Z_a x| Z_k."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
                cands.append((a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _group(N, spec):
    """Multiplication table M[x][y] = x*y for the group named by spec, as a numpy array."""
    if spec[0] == "cyc":
        _, mul, _ = lib.cyclic_group(N)
    else:
        a, k, r = spec
        _, mul, _ = lib.semidirect_group(a, k, r)
    return np.array([[mul(x, y) for y in range(N)] for x in range(N)], dtype=np.int64)


def _counts(m, d):
    """Circulant m x m count matrix with all row and column sums equal to d."""
    q, r = divmod(d, m)
    return [[q + (1 if (j - i) % m < r else 0) for j in range(m)] for i in range(m)]


def _build_matrix(m, N, M, blocks, darts):
    """Dense adjacency matrix (with identity added) for the current darts."""
    mN = m * N
    E = np.eye(2 * mN, dtype=np.float32)
    xs = np.arange(N)
    for (i, j, _), gs in zip(blocks, darts):
        rows = i * N + xs
        for g in gs:
            cols = mN + j * N + M[:, g]
            E[rows, cols] = 1.0
            E[cols, rows] = 1.0
    return E


def _bad(m, N, E):
    """Number of (orbit representative, vertex) pairs at distance greater than 3."""
    reps = [i * N for i in range(m)] + [m * N + j * N for j in range(m)]
    P = E[reps]
    P3 = (P @ E) @ E
    return int(np.count_nonzero(P3 < 0.5))


def _attempt(m, N, tabs, blocks, rng, deadline):
    """Anneal darts until the diameter-3 cost is zero. Returns (M, darts) or None."""
    if not blocks:
        return None
    maxc = max(c for _, _, c in blocks)
    if N <= maxc:
        return None
    nb = len(blocks)
    iters = 3000
    r = 0
    while time.monotonic() < deadline:
        M = tabs[r % len(tabs)]
        r += 1
        darts = [rng.sample(range(N), c) for _, _, c in blocks]
        cost = _bad(m, N, _build_matrix(m, N, M, blocks, darts))
        for it in range(iters):
            if cost == 0:
                return M, darts
            if (it & 31) == 0 and time.monotonic() >= deadline:
                return None
            temp = 1.5 * (0.02 ** (it / iters)) + 0.01
            b = rng.randrange(nb)
            k = rng.randrange(blocks[b][2])
            cur = darts[b]
            g = rng.randrange(N)
            if g in cur:
                continue
            old = cur[k]
            cur[k] = g
            new_cost = _bad(m, N, _build_matrix(m, N, M, blocks, darts))
            delta = new_cost - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = new_cost
            else:
                cur[k] = old
    return None


def _edges(m, N, M, blocks, darts):
    """Edge list and order for the lift defined by blocks and darts."""
    mN = m * N
    edges = []
    for (i, j, _), gs in zip(blocks, darts):
        for g in gs:
            col = M[:, g]
            for x in range(N):
                edges.append((i * N + x, mN + j * N + int(col[x])))
    return 2 * mN, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D < 3 or d < 2:
        return best

    try:
        # Known record family for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                if n_a > best[0] and lib.is_valid(n_a, e_a, d, D):
                    best = (n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
    except Exception:
        pass

    try:
        if D == 3 and d >= 3:
            upper = d * (d - 1) + 1          # T = m*N, order 2T <= Moore bound
            lo = best[0] // 2 + 1            # need 2T > current best
            if lo <= upper:
                counts = _counts(0, 1) if False else None
                all_ms = {}
                for T in range(lo, upper + 1):
                    all_ms[T] = [m for m in range(1, 9) if T % m == 0 and T // m >= 2]

                T = lo
                while T <= upper and time.monotonic() < deadline:
                    ms = list(all_ms[T])
                    rng.shuffle(ms)
                    for pos, m in enumerate(ms):
                        now = time.monotonic()
                        if now >= deadline:
                            break
                        left = sum(len(all_ms[t]) for t in range(T, upper + 1)) - pos
                        budget = min(8.0, max(0.5, (deadline - now) / max(1, left)))
                        N = T // m
                        blocks_all = _counts(m, d)
                        blocks = [(i, j, blocks_all[i][j]) for i in range(m)
                                  for j in range(m) if blocks_all[i][j] > 0]
                        specs = _specs(N, rng)
                        tabs = []
                        for spec in specs:
                            try:
                                tabs.append(_group(N, spec))
                            except Exception:
                                pass
                        if not tabs:
                            continue
                        res = _attempt(m, N, tabs, blocks, rng, now + budget)
                        if res is not None:
                            M, darts = res
                            n, e = _edges(m, N, M, blocks, darts)
                            if n > best[0] and lib.is_valid(n, e, d, D):
                                best = (n, e)
                            break
                    T += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
