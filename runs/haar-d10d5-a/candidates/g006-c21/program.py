"""Bipartite lifts over a 2x2 base (not a plain Haar graph) for the d=10, D=5 target.

THEORY.  Take a finite group G (order N, element 0 = identity, multiplication table MT, MT[x, g] = x*g).
The base graph has four classes A0, A1, B0, B1.  Each base pair (Ai, Bj) carries 5 darts with voltages
V_ij (distinct elements of G).  The lift has 4N vertices (class c, element x), with edges
(Ai, x) ~ (Bj, x*g) for every dart (i, j, g).  Every vertex has degree 10 and the graph is bipartite.

Left multiplication by t is an automorphism of the lift, so the vertices of each class are all equivalent.
Hence the diameter is at most 5 iff, for each of the four classes c, every vertex is within distance 5 of
(c, identity).  Four BFS runs give the cost (number of uncovered vertices).  Cost 0 means valid.

SEARCH.  Simulated annealing over the 20 voltages, with one voltage changed per move.  Groups are
non-abelian metacyclic groups of order between 896 and 1000, so the lift has at least 3584 vertices and
beats the Haar fallback of 3582.  Every result is checked with lib.is_valid before it is returned.  If
nothing verifies, the parent's valid Haar graph (3582 vertices) is returned.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
N_LO, N_HI = 896, 1000     # group orders tried (lift order = 4 * N)
PICKS = 6                  # number of groups given search time
DIAM = 5
DEG = 10
TEMP = 0.8
PATIENCE = 3000

DART_I = [0] * 10 + [1] * 10
DART_J = [0] * 5 + [1] * 5 + [0] * 5 + [1] * 5
A_DARTS = [[t for t in range(20) if DART_I[t] == i] for i in (0, 1)]
B_DARTS = [[t for t in range(20) if DART_J[t] == j] for j in (0, 1)]


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
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
    return _finish(MT)


def candidate_groups(lo, hi):
    """One non-abelian metacyclic group per order N in [lo, hi], as (N, m, k, lam)."""
    out = []
    for N in range(lo, hi + 1):
        found = None
        for k in range(2, N // 2 + 1):
            if N % k:
                continue
            m = N // k
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    found = (m, k, lam)
                    break
            if found:
                break
        if found:
            out.append((N,) + found)
    return out


def pick_spread(cands, count):
    if len(cands) <= count:
        return list(cands)
    idx = np.unique(np.linspace(0, len(cands) - 1, count).round().astype(int))
    return [cands[i] for i in idx]


# ------------------------------------------------------------------------- lift search

def _uncovered(adj, start, n):
    """Vertices not within DIAM steps of start, using the adjacency array adj (n x DEG)."""
    vis = np.zeros(n, dtype=bool)
    vis[start] = True
    front = np.array([start], dtype=np.int64)
    for _ in range(DIAM):
        nxt = np.zeros(n, dtype=bool)
        nxt[adj[front].ravel()] = True
        nxt &= ~vis
        vis |= nxt
        front = np.flatnonzero(nxt)
        if front.size == 0:
            break
    return n - int(vis.sum())


def _cost(MT, inv, V, N):
    n = 4 * N
    adj = np.empty((n, DEG), dtype=np.int64)
    for i in (0, 1):
        for k, t in enumerate(A_DARTS[i]):
            adj[i * N:(i + 1) * N, k] = (2 + DART_J[t]) * N + MT[:, V[t]]
    for j in (0, 1):
        for k, t in enumerate(B_DARTS[j]):
            adj[(2 + j) * N:(3 + j) * N, k] = DART_I[t] * N + MT[:, inv[V[t]]]
    return sum(_uncovered(adj, s, n) for s in (0, N, 2 * N, 3 * N))


def anneal(MT, inv, deadline, rng):
    """Anneal the 20 voltages until cost 0 or the deadline.  Returns voltage array or None."""
    N = MT.shape[0]

    def new_V():
        return np.concatenate([rng.choice(N, 5, replace=False) for _ in range(4)]).astype(np.int64)

    V = new_V()
    cur = _cost(MT, inv, V, N)
    bestc, bestV = cur, V.copy()
    since = 0
    while cur > 0 and time.monotonic() < deadline:
        if since > PATIENCE:
            V = new_V()
            cur = _cost(MT, inv, V, N)
            since = 0
            if cur < bestc:
                bestc, bestV = cur, V.copy()
            continue
        t = int(rng.integers(DARTS := 20))
        p = t // 5
        x = int(rng.integers(N))
        if np.any(V[5 * p:5 * p + 5] == x):
            since += 1
            continue
        old = V[t]
        V[t] = x
        c = _cost(MT, inv, V, N)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            cur = c
            if cur < bestc:
                bestc, bestV, since = cur, V.copy(), 0
            else:
                since += 1
        else:
            V[t] = old
            since += 1
    return bestV if bestc == 0 else None


def lift_edges(MT, V):
    """Edges of the 4N-vertex lift.  Class c vertex x has id c*N + x; B-classes are 2 and 3."""
    N = MT.shape[0]
    edges = []
    for t in range(20):
        i, j = DART_I[t], DART_J[t]
        col = MT[:, int(V[t])].tolist()
        a0, b0 = i * N, (2 + j) * N
        edges.extend((a0 + x, b0 + col[x]) for x in range(N))
    return 4 * N, edges


# ----------------------------------------------------------------------- fallbacks

def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# Valid Haar graph on 3582 vertices (order 1791 group), used only if no lift verifies.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


# --------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end = t0 + 0.70 * time_limit
    rng = np.random.default_rng(seed)
    picks = pick_spread(candidate_groups(N_LO, N_HI), PICKS)
    best, best_n = None, 0
    for idx, (N, m, k, lam) in enumerate(picks):
        if 4 * N <= best_n:
            continue
        now = time.monotonic()
        left = end - now
        if left < 1.0:
            break
        slot = left / (len(picks) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            V = anneal(MT, inv, now + slot, rng)
            if V is not None:
                n, edges = lift_edges(MT, V)
                if lib.is_valid(n, edges, d, D):
                    best, best_n = (n, edges), n
        except Exception:
            continue
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
