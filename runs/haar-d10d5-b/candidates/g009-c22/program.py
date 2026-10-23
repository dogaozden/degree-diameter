"""Bipartite degree-diameter search, diameter 5, d = 10: a two-orbit group lift.

CONSTRUCTION.  Take a group G of order N (metacyclic Z_m x| Z_k) and four base
vertices A_0, A_1, B_0, B_1.  Each cell (i, j) carries h = d/2 group elements S[i][j].
Vertices are (A_i, g) and (B_j, g).  Edges are (A_i, g) ~ (B_j, g*s) for s in S[i][j].
This gives a bipartite d-regular graph on 4N vertices.

Left multiplication by any k in G is an automorphism, so each of the four orbits is
transitive.  The diameter is therefore at most 5 iff a depth-5 BFS from the four
representatives (A_0, e), (A_1, e), (B_0, e), (B_1, e) reaches every vertex.  The cost
is the total number of unreached vertices.  Simulated annealing on the 4*h group
elements drives the cost to 0.

SAFETY.  Only a graph that passes lib.is_valid is returned.  If annealing fails, the
validated Haar fallback (order 3582) is returned.  Any other (d, D) gets a small valid
graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def metacyclic_candidates(lo, hi):
    """(order, m, k, lam) for non-abelian metacyclic groups with order in [lo, hi], smallest first."""
    out = []
    for k in range(2, 41):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            if m * k < lo or m * k > hi:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((m * k, m, k, lam))
                    break
    out.sort()
    return out


# ------------------------------------------------------------------- two-orbit lift

def make_adj(MT, inv, S, N, h):
    """Adjacency array (4N, 2h). Ids: A_i,g = i*N+g ; B_j,g = 2N + j*N + g."""
    adj = np.empty((4 * N, 2 * h), dtype=np.int64)
    for i in range(2):
        for j in range(2):
            for t in range(h):
                s = int(S[i, j, t])
                adj[i * N:(i + 1) * N, j * h + t] = 2 * N + j * N + MT[:, s]
                adj[2 * N + j * N:2 * N + (j + 1) * N, i * h + t] = i * N + MT[:, inv[s]]
    return adj


def cost(adj, n, N):
    """Total unreached vertices over depth-5 BFS from the four orbit representatives."""
    total = 0
    for r in (0, N, 2 * N, 3 * N):
        seen = np.zeros(n, dtype=bool)
        seen[r] = True
        fr = np.array([r], dtype=np.int64)
        for _ in range(5):
            nb = adj[fr].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            fr = nb
        total += n - int(np.count_nonzero(seen))
    return total


def anneal(MT, inv, N, h, deadline, rng, K=4, temp=1.0, patience=2500):
    """Anneal the 4 cells of h group elements. Returns (best S, best cost)."""
    n = 4 * N
    bestS, bestc = None, 10 ** 9

    def fresh():
        S = np.empty((2, 2, h), dtype=np.int64)
        for i in range(2):
            for j in range(2):
                S[i, j] = rng.choice(N, h, replace=False)
        return S

    S = fresh()
    cur = cost(make_adj(MT, inv, S, N, h), n, N)
    since = 0
    while time.monotonic() < deadline:
        if cur < bestc:
            bestc, bestS, since = cur, S.copy(), 0
        if cur == 0:
            break
        if since > patience:
            S = fresh()
            cur = cost(make_adj(MT, inv, S, N, h), n, N)
            since = 0
            continue
        i = int(rng.integers(2))
        j = int(rng.integers(2))
        t = int(rng.integers(h))
        pick = None
        for x in rng.integers(0, N, size=K):
            x = int(x)
            if x in S[i, j]:
                continue
            old = int(S[i, j, t])
            S[i, j, t] = x
            adj2 = make_adj(MT, inv, S, N, h)
            c = cost(adj2, n, N)
            S[i, j, t] = old
            if pick is None or c < pick[0]:
                pick = (c, x)
        since += 1
        if pick is None:
            continue
        c, x = pick
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i, j, t] = x
            cur = c
    if cur < bestc:
        bestc, bestS = cur, S.copy()
    return bestS, bestc


def edges_from(adj, N):
    """Edge list from the A-side rows of the adjacency array (each edge appears once)."""
    return [(u, int(v)) for u in range(2 * N) for v in adj[u]]


# ------------------------------------------------------------------ Haar fallback

def haar_edges(MT, S):
    """Haar graph edges: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Validated Haar graph of order 3582 for the target; trivial graph otherwise."""
    try:
        MT, _ = group_meta(199, 9, 180)
        S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
        n, edges = haar_edges(MT, S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# ---------------------------------------------------------------------------- driver

TARGET = (10, 5)


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + min(0.80 * time_limit, time_limit - 8.0)
    rng = np.random.default_rng(seed)
    h = d // 2
    groups = metacyclic_candidates(1001, 1100)[:4]
    for idx, (N, m, k, lam) in enumerate(groups):
        now = time.monotonic()
        if now >= deadline - 1.0:
            break
        end = now + (deadline - now) / (len(groups) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = anneal(MT, inv, N, h, end, rng)
            if S is not None and c == 0:
                edges = edges_from(make_adj(MT, inv, S, N, h), N)
                if lib.is_valid(4 * N, edges, d, D):
                    return 4 * N, edges
        except Exception:
            continue
    return _fallback(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return run(d, D, seed, time_limit)
    except Exception:
        return _fallback(d, D)
