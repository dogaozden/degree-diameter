"""Voltage-lift search for the bipartite degree-diameter problem (d=6, D=5), with a verified fallback.

CONSTRUCTION.  Base graph: two A-vertices and two B-vertices.  Choose a group G of order N and sets S_ij of
group elements with |S_ij| = m_ij, where m = [[a, 6-a], [6-a, a]] so every base vertex has degree 6.  The lift
has 4N vertices: A_i fibre i*N+g and B_j fibre 2N+j*N+h, with edges (A_i, g) ~ (B_j, g*s) for s in S_ij.
Left multiplication by any element of G is an automorphism, so each fibre is one orbit.  Therefore the diameter
is at most 5 iff every vertex is within distance 5 of the four fibre representatives (A_0, e), (A_1, e), (B_0, e),
(B_1, e).  The cost is the total number of vertices left uncovered by those four BFS balls, and the graph is valid
exactly when the cost is 0.  Simulated annealing (best of K single-slot moves, Metropolis acceptance, restarts)
searches the voltage sets over metacyclic groups of order 172..230, so the lift has 688+ vertices, above the
record 684.

SAFETY.  Only a graph that passes lib.is_valid is returned.  If the search finds nothing in its budget, the
verified 660-vertex Haar graph (group_meta(33, 10, 26)) is returned.  Other (d, D) cases use the trivial graphs.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)


# ----------------------------------------------------------------------------- groups and helper graphs

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


# ----------------------------------------------------------------------------- voltage-lift search

def _meta_candidates(lo, hi):
    """Metacyclic groups Z_m x|_lam Z_k of order N in [lo, hi], k in 2..8, lam != 1 (non-abelian), ascending N."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, 9):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lams = [l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1 % m]
            for lam in lams[:2]:
                out.append((N, m, k, lam))
    return out


def _adj(MT, inv, N, S):
    """Adjacency array (4N x 6) of the 2+2 voltage lift for voltage sets S[i][j]."""
    g = np.arange(N)
    adj = np.empty((4 * N, 6), dtype=np.int64)
    for i in range(2):
        off = 0
        for j in range(2):
            s = np.asarray(S[i][j], dtype=np.int64)
            adj[i * N:(i + 1) * N, off:off + len(s)] = 2 * N + j * N + MT[g[:, None], s[None, :]]
            off += len(s)
    for j in range(2):
        off = 0
        for i in range(2):
            s = np.asarray(S[i][j], dtype=np.int64)
            adj[2 * N + j * N:2 * N + (j + 1) * N, off:off + len(s)] = i * N + MT[g[:, None], inv[s][None, :]]
            off += len(s)
    return adj


def _uncovered(adj, n, sources, D):
    """Total number of vertices not within distance D of the given source vertices."""
    tot = 0
    for src in sources:
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[front].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            front = np.unique(nb)
            seen[front] = True
        tot += n - int(seen.sum())
    return tot


def _anneal(MT, inv, N, a, rng, end, K=6, T=1.0, patience=400):
    """Anneal voltage sets for the 2+2 lift with multiplicities [[a, 6-a], [6-a, a]].
    Returns S (cost 0) or None if the deadline passes first."""
    m = [[a, 6 - a], [6 - a, a]]
    n = 4 * N
    sources = [0, N, 2 * N, 3 * N]

    def random_sets():
        return [[sorted(rng.choice(N, m[i][j], replace=False).tolist()) for j in range(2)] for i in range(2)]

    def cost_of(S):
        return _uncovered(_adj(MT, inv, N, S), n, sources, 5)

    S = random_sets()
    cur = cost_of(S)
    best_c, since = cur, 0
    while time.monotonic() < end:
        if cur == 0:
            return S
        best_mv, best_v = None, None
        for _ in range(K):
            i = int(rng.integers(2))
            j = int(rng.integers(2))
            pos = int(rng.integers(m[i][j]))
            x = int(rng.integers(N))
            if x in S[i][j]:
                continue
            old = S[i][j][pos]
            S[i][j][pos] = x
            c = cost_of(S)
            S[i][j][pos] = old
            if best_v is None or c < best_v:
                best_v, best_mv = c, (i, j, pos, x)
        if best_mv is None:
            continue
        delta = best_v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            i, j, pos, x = best_mv
            S[i][j][pos] = x
            cur = best_v
            if cur < best_c:
                best_c, since = cur, 0
            else:
                since += 1
        else:
            since += 1
        if since > patience:
            S = random_sets()
            cur = cost_of(S)
            best_c, since = cur, 0
    return None


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.6 * time_limit
    rng = np.random.default_rng(seed)
    cands = _meta_candidates(172, 230)
    for idx, (N, m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
        except Exception:
            continue
        a = int(rng.choice([1, 2, 3, 3, 4, 5]))
        try:
            S = _anneal(MT, inv, N, a, rng, end)
        except Exception:
            S = None
        if S is None:
            continue
        try:
            adj = _adj(MT, inv, N, S)
            n = 4 * N
            edges = [(v, int(u)) for v in range(2 * N) for u in adj[v].tolist()]
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
