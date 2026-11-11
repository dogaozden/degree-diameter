"""Lifted-group search for the bipartite degree-diameter problem (numpy + lib only).

Parent approach: Haar graphs (one base vertex per side). This program searches a different family: group lifts
of a p-vertex-per-side base multigraph over a metacyclic group G = Z_m x| Z_k. Vertices (i, x) and (j, y) for
i, j in range(p) and x, y in G; for each pair (i, j) a set S_ij of c_ij group elements gives the edges
(i, x) ~ (j, x*s) for s in S_ij. Every row and column sums to d, so the graph is bipartite and d-regular with
2pM vertices.

Left multiplication by h in G is an automorphism, so distances from (i, x) equal distances from (i, e) to the
shifted target. The diameter is therefore at most D iff every base-vertex representative (one per side per base
vertex) reaches all vertices within D steps. The cost is the number of unreached (source, vertex) pairs, summed
over the 2p representatives. Cost 0 means valid. Each evaluation is a few batched boolean BFS steps in numpy.

Simulated annealing on the S_ij sets (best of K single-slot moves per step, with restarts). Only zero-cost graphs
are returned, each checked with lib.is_valid. Otherwise the parent's valid Haar graph of order 3582 is returned.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)


# ------------------------------------------------------------------------------------------ groups

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with element (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).
    Returns (MT, inv): MT[g, h] = g*h, inv[g] = g^-1; element 0 is the identity. Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
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


def metacyclic_groups(lo, hi, kmax=60, want=2):
    """Up to `want` triples (m, k, lam) with m*k = M for the smallest M in [lo, hi] that admits one.
    The group is nonabelian (lam != 1)."""
    out = []
    for M in range(lo, hi + 1):
        found = None
        for k in range(2, min(kmax, M // 3) + 1):
            if M % k:
                continue
            m = M // k
            lam = next((x for x in range(2, m) if pow(x, k, m) == 1), None)
            if lam is not None:
                found = (m, k, lam)
                break
        if found is not None:
            out.append(found)
            if len(out) >= want:
                break
    return out


# ------------------------------------------------------------------------------- lift construction

def lift_nbr(MTT, inv, sets, p, M, d):
    """Neighbour table (V, d) of the lift. A-vertex (i, x) has id i*M + x, B-vertex (j, y) has id p*M + j*M + y.
    MTT is the transpose of the table, so MTT[s][x] = x*s."""
    V = 2 * p * M
    nbr = np.empty((V, d), dtype=np.int32)
    for i in range(p):
        cols = []
        for j in range(p):
            for s in sets[i][j]:
                cols.append(p * M + j * M + MTT[s])
        nbr[i * M:(i + 1) * M] = np.stack(cols, axis=1)
    for j in range(p):
        cols = []
        for i in range(p):
            for s in sets[i][j]:
                cols.append(i * M + MTT[inv[s]])
        nbr[p * M + j * M:p * M + (j + 1) * M] = np.stack(cols, axis=1)
    return nbr


def lift_cost(nbr, p, M, D):
    """Number of (representative, vertex) pairs at distance > D, over the 2p base representatives.
    Zero means the lift has diameter at most D (fibre transitivity reduces the check to these sources)."""
    V = nbr.shape[0]
    src = [i * M for i in range(p)] + [p * M + j * M for j in range(p)]
    S = len(src)
    R = np.zeros((V, S), dtype=bool)
    R[src, np.arange(S)] = True
    for _ in range(D):
        R = R | R[nbr].any(axis=1)
    return V * S - int(R.sum())


def lift_edges(MTT, p, M, sets):
    edges = []
    xs = np.arange(M)
    for i in range(p):
        for j in range(p):
            for s in sets[i][j]:
                a = i * M + xs
                b = p * M + j * M + MTT[s]
                edges.extend(zip(a.tolist(), b.tolist()))
    return 2 * p * M, edges


def copy_sets(sets):
    return [[list(s) for s in row] for row in sets]


def anneal(rng, MT_inv, p, M, counts, d, D, deadline, K=6, temp=2.0, patience=400):
    """Simulated annealing on the S_ij sets. Returns (best cost, best sets)."""
    MTT, inv = MT_inv

    def fresh():
        return [[rng.choice(M, size=counts[i][j], replace=False).tolist() for j in range(p)]
                for i in range(p)]

    def evaluate(sets):
        return lift_cost(lift_nbr(MTT, inv, sets, p, M, d), p, M, D)

    sets = fresh()
    cur = evaluate(sets)
    best_c, best = cur, copy_sets(sets)
    run_best, stale = cur, 0
    cells = [(i, j) for i in range(p) for j in range(p)]
    while cur > 0 and time.monotonic() < deadline:
        moves = []
        for _ in range(K):
            i, j = cells[int(rng.integers(len(cells)))]
            t = int(rng.integers(counts[i][j]))
            x = int(rng.integers(M))
            if x not in sets[i][j]:
                moves.append((i, j, t, x))
        if not moves:
            continue
        bc, bm = None, None
        for (i, j, t, x) in moves:
            old = sets[i][j][t]
            sets[i][j][t] = x
            c = evaluate(sets)
            sets[i][j][t] = old
            if bc is None or c < bc:
                bc, bm = c, (i, j, t, x)
        delta = bc - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            i, j, t, x = bm
            sets[i][j][t] = x
            cur = bc
        if cur < best_c:
            best_c, best = cur, copy_sets(sets)
        if cur < run_best:
            run_best, stale = cur, 0
        else:
            stale += 1
        if stale > patience:
            sets = fresh()
            cur = evaluate(sets)
            run_best, stale = cur, 0
            if cur < best_c:
                best_c, best = cur, copy_sets(sets)
    return best_c, best


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + 0.70 * time_limit
    rng = np.random.default_rng(seed)
    # (base vertices per side p, circulant row weights summing to d, order range for the group, time share)
    configs = [
        (2, [5, 5], 1001, 1100, 0.40),
        (3, [4, 3, 3], 667, 700, 0.30),
        (5, [2, 2, 2, 2, 2], 401, 440, 0.30),
    ]
    slots = []
    for p, w, lo, hi, share in configs:
        groups = metacyclic_groups(lo, hi, want=2)
        for grp in groups:
            slots.append((p, w, grp, share / len(groups)))
    for idx, (p, w, grp, share) in enumerate(slots):
        now = time.monotonic()
        if now >= deadline_all:
            break
        rest = sum(s[3] for s in slots[idx:])
        end = now + (deadline_all - now) * share / rest
        m, k, lam = grp
        MT, inv = group_meta(m, k, lam)
        MTT = np.ascontiguousarray(MT.T)
        M = m * k
        counts = [[w[(j - i) % p] for j in range(p)] for i in range(p)]
        c, sets = anneal(rng, (MTT, inv), p, M, counts, d, D, end)
        if c == 0:
            n, edges = lift_edges(MTT, p, M, sets)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


# ------------------------------------------------------------------------------ fallbacks

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def fallback_target(d, D):
    """Valid Haar graph of order 3582 (checked), used when no lift reaches cost 0."""
    try:
        MT, _ = group_meta(199, 9, 180)
        n, edges = haar_edges(MT, [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return 2 * d, [(a, d + b) for a in range(d) for b in range(d)]   # K_{d,d}: diameter 2


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        res = run_target(d, D, seed, time_limit)
        if res is not None:
            return res
    except Exception:
        pass
    return fallback_target(d, D)
