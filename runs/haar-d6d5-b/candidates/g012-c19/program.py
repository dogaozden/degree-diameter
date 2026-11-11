"""Bold variant for d=6, D=5: voltage lifts of small bases over dihedral groups, with a checked Haar fallback.

Construction: a base bipartite multigraph on k A-vertices and k B-vertices, each of degree d (a sum of d random
permutation matrices), with every dart (i, j, s) joining A^i_g to B^j_{s*g} for all g in G.  Right multiplication
is an automorphism, so each orbit is transitive and the diameter is at most D iff a BFS of depth D from one
representative of each orbit reaches every vertex.  Voltages are annealed to make that cost zero.  Only a graph
that passes lib.is_valid is returned; otherwise a precomputed valid Haar graph (660 vertices) is returned.
"""
import math
import time

import numpy as np

import lib


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


# ------------------------------------------------------------------------------- voltage-lift search

def random_pattern(k, d, rng):
    """k x k multiplicity matrix with all row and column sums equal to d (sum of d permutation matrices)."""
    P = np.zeros((k, k), dtype=np.int64)
    for _ in range(d):
        P[np.arange(k), rng.permutation(k)] += 1
    return P


def pattern_entries(P):
    """Flatten a multiplicity matrix into aligned arrays I (A-index) and J (B-index), one entry per dart."""
    k = P.shape[0]
    I, J = [], []
    for i in range(k):
        for j in range(k):
            for _ in range(int(P[i, j])):
                I.append(i)
                J.append(j)
    return np.array(I, dtype=np.int64), np.array(J, dtype=np.int64)


def random_voltages(I, J, M, rng):
    """Voltages S aligned with I, J; darts on the same (i, j) pair get distinct voltages (no parallel edges)."""
    S = np.empty(len(I), dtype=np.int64)
    for i, j in set(zip(I.tolist(), J.tolist())):
        idx = np.nonzero((I == i) & (J == j))[0]
        S[idx] = rng.choice(M, len(idx), replace=False)
    return S


def lift_nbr(I, J, S, MT, inv, k, M, d):
    """Neighbour table (n, d): A^i_g is index i*M+g, B^j_h is index k*M + j*M + h."""
    n = 2 * k * M
    off_B = k * M
    nbr = np.empty((n, d), dtype=np.int64)
    for i in range(k):
        idx = np.nonzero(I == i)[0]
        rows = slice(i * M, (i + 1) * M)
        for t, e in enumerate(idx):
            nbr[rows, t] = off_B + J[e] * M + MT[S[e]]          # A^i_g ~ B^j_{s g}
    for j in range(k):
        idx = np.nonzero(J == j)[0]
        rows = slice(off_B + j * M, off_B + (j + 1) * M)
        for t, e in enumerate(idx):
            nbr[rows, t] = I[e] * M + MT[inv[S[e]]]             # B^j_h ~ A^i_{s^-1 h}
    return nbr


def lift_cost(nbr, sources, n, D):
    """Total number of vertices NOT within distance D of the given orbit representatives (0 = valid)."""
    total = 0
    for s in sources:
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = nbr[front].ravel()
            nb = np.unique(nb[~seen[nb]])
            if nb.size == 0:
                break
            seen[nb] = True
            front = nb
        total += n - int(seen.sum())
    return total


def anneal(k, M, d, D, MT, inv, deadline, rng):
    """Anneal voltages over random patterns until the lift has cost 0 or the deadline passes.
    Returns ((I, J, S), cost) for the best state seen."""
    n = 2 * k * M
    sources = [i * M for i in range(k)] + [k * M + j * M for j in range(k)]
    best_state, best_c = None, 10 ** 9
    while time.monotonic() < deadline:
        P = random_pattern(k, d, rng)
        I, J = pattern_entries(P)
        S = random_voltages(I, J, M, rng)
        cur = lift_cost(lift_nbr(I, J, S, MT, inv, k, M, d), sources, n, D)
        if cur < best_c:
            best_c, best_state = cur, (I.copy(), J.copy(), S.copy())
        if cur == 0:
            return best_state, 0
        T = 1.0
        rbest, since = cur, 0
        E = len(I)
        while time.monotonic() < deadline and since < 4000:
            e = int(rng.integers(E))
            i, j = I[e], J[e]
            used = S[(I == i) & (J == j)]
            new = int(rng.integers(M))
            if new in used:
                continue
            old = S[e]
            S[e] = new
            c = lift_cost(lift_nbr(I, J, S, MT, inv, k, M, d), sources, n, D)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                if cur < best_c:
                    best_c, best_state = cur, (I.copy(), J.copy(), S.copy())
                if cur == 0:
                    return best_state, 0
            else:
                S[e] = old
            if cur < rbest:
                rbest, since = cur, 0
            else:
                since += 1
    return best_state, best_c


def lift_graph(I, J, S, MT, k, M):
    """Explicit (n, edges) of the lift."""
    n = 2 * k * M
    edges = []
    for e in range(len(I)):
        for g in range(M):
            a = int(I[e]) * M + g
            b = k * M + int(J[e]) * M + int(MT[S[e], g])
            edges.append((a, b))
    return n, edges


# ----------------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def haar_fallback(d, D):
    """Valid Haar graph on 660 vertices for (6, 5); checked before returning."""
    MT, _ = group_meta(33, 10, 26)
    S = [0, 179, 116, 180, 47, 306]
    N = MT.shape[0]
    edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
    n = 2 * N
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


# ----------------------------------------------------------------------------------------- build

TARGET = (6, 5)
# (k, M): base with k A- and k B-vertices, group order M (dihedral of order M, M even).  Ordered by vertex count.
# Each lift has 2*k*M vertices: 688, 688, 696, 700 (record 684).
CANDIDATES = [(2, 172), (4, 86), (3, 116), (5, 70)]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end_all = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)
    for idx, (k, M) in enumerate(CANDIDATES):
        now = time.monotonic()
        if now >= end_all:
            break
        slice_end = now + (end_all - now) / (len(CANDIDATES) - idx)
        try:
            MT, inv = group_meta(M // 2, 2, M // 2 - 1)   # dihedral group of order M
            state, c = anneal(k, M, d, D, MT, inv, slice_end, rng)
        except Exception:
            continue
        if state is not None and c == 0:
            try:
                I, J, S = state
                n, edges = lift_graph(I, J, S, MT, k, M)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass
    try:
        g = haar_fallback(d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
