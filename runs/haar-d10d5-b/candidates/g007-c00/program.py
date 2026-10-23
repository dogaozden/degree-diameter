"""Two-orbit Haar-type lifts for the bipartite degree-diameter problem at (d=10, D=5).

Idea. Let G be a finite group of order N. Use four vertex orbits: A0, A1, B0, B1, each a copy of G.
Each dart (i, j, s) with i, j in {0, 1} and s in G gives the edges (g, A_i) ~ (s*g, B_j) for all g in G.
Right multiplication by any h in G is an automorphism, and it acts transitively on each orbit. So the
diameter is at most D iff a BFS from one representative of each orbit reaches all 4N vertices within D steps.
The graph has 4N vertices and is d-regular when every A_i and every B_j receives exactly d darts.

Search. Start from random dart sets with a fixed split of counts (k, d-k, d-k, k), and anneal on the number
of unreached vertices summed over the four representatives. Each step changes one dart's group element.
A zero-cost result is rebuilt and checked with lib.is_valid. Group orders N = 1001, 1002, ... are tried in
increasing order, so any valid result gives at least 4004 vertices, which beats the record of 4000.

Safe fallback. If nothing verifies, the previously verified 3582-vertex Haar graph is returned.
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


def group_cyclic(N):
    """Cyclic group Z_N with identity 0."""
    a = np.arange(N, dtype=np.int64)
    MT = ((a[:, None] + a[None, :]) % N).astype(np.int32)
    return _finish(MT)


# ------------------------------------------------------------------------------------ two-orbit lift

def build_adj(MT, inv, darts, N, d):
    """Adjacency (V x d) of the two-orbit lift. Orbit index: A_i g -> i*N+g, B_j g -> 2N+j*N+g.
    Dart (i, j, s) gives (A_i g) ~ (B_j, s*g) for every g."""
    V = 4 * N
    adj = np.empty((V, d), dtype=np.int64)
    sA = [0, 0]
    sB = [0, 0]
    g = np.arange(N, dtype=np.int64)
    for i, j, s in darts:
        adj[i * N + g, sA[i]] = 2 * N + j * N + MT[s].astype(np.int64)
        adj[2 * N + j * N + g, sB[j]] = i * N + MT[int(inv[s])].astype(np.int64)
        sA[i] += 1
        sB[j] += 1
    return adj


def cost(adj, N, D):
    """Total number of vertices not reached within D steps from the four orbit representatives."""
    V = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = np.zeros(V, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[front].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            front = nb
        total += V - int(seen.sum())
    return total


def anneal(MT, inv, N, d, D, deadline, rng, T=0.6, patience=2500):
    """Anneal dart sets for the two-orbit lift until cost 0 or the deadline. Returns (darts, cost)."""
    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        k = int(rng.integers(3, 8))  # darts A0->B0 and A1->B1 count; 3..7 keeps every count positive
        pairs = [(0, 0, k), (0, 1, d - k), (1, 0, d - k), (1, 1, k)]
        darts = []
        for i, j, c in pairs:
            for s in rng.choice(N, c, replace=False):
                darts.append([i, j, int(s)])
        cur = cost(build_adj(MT, inv, darts, N, d), N, D)
        if cur < bestc:
            best, bestc = [list(x) for x in darts], cur
        since = 0
        while cur > 0 and time.monotonic() < deadline and since < patience:
            t = int(rng.integers(len(darts)))
            i, j, old = darts[t]
            used = {s for a, b, s in darts if a == i and b == j}
            s_new = int(rng.integers(N))
            if s_new in used:
                since += 1
                continue
            darts[t][2] = s_new
            c = cost(build_adj(MT, inv, darts, N, d), N, D)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                if cur < bestc:
                    best, bestc = [list(x) for x in darts], cur
                    since = 0
                else:
                    since += 1
            else:
                darts[t][2] = old
                since += 1
        if bestc == 0:
            return best, 0
    return best, bestc


def build_graph(MT, inv, N, darts, d, D):
    """Edges of the two-orbit lift for these darts, or None if lib.is_valid rejects them."""
    adj = build_adj(MT, inv, darts, N, d)
    n = 4 * N
    edges = [(v, int(u)) for v in range(2 * N) for u in adj[v]]
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def candidate_groups(N):
    """Builders for groups of order N: up to two metacyclic Z_m x| Z_k, then the cyclic group."""
    specs = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                specs.append(lambda m=m, k=k, lam=lam: group_meta(m, k, lam))
                break
        if len(specs) >= 2:
            break
    specs.append(lambda N=N: group_cyclic(N))
    return specs


# ------------------------------------------------------------------------- shared fallbacks

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


TARGET = (10, 5)
# Verified 3582-vertex Haar graph, used only if no two-orbit lift is found in time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end = t0 + 0.72 * time_limit
    slice_len = max(2.0, 0.12 * time_limit)
    rng = np.random.default_rng(seed)
    best = None
    best_n = 0

    for N in range(1001, 1200):
        if time.monotonic() >= end - 0.5:
            break
        for builder in candidate_groups(N):
            now = time.monotonic()
            if now >= end - 0.5:
                break
            try:
                MT, inv = builder()
            except Exception:
                continue
            darts, c = anneal(MT, inv, N, d, D, min(end, now + slice_len), rng)
            if c == 0 and darts is not None:
                g = build_graph(MT, inv, N, darts, d, D)
                if g is not None and g[0] > best_n:
                    best, best_n = g, g[0]
                    break

    if best is not None:
        return best
    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
