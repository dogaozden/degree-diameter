"""Bold variant for d=10, D=5: a 2x2 voltage lift (four base vertices, A_0 A_1 | B_0 B_1) over a
metacyclic group of order about 1000-1060, instead of a Haar graph.

Each pair (A_i, B_j) carries 5 voltages S[i][j]. Vertex (c, x) with c in {0,1,2,3} is joined to
(2+j, x*s) for every voltage s in S[c][j] (c = i < 2), and the B side uses inverses. Left
multiplication is an automorphism, so the diameter is 5 iff every one of the four base classes
reaches all 4N vertices within 5 steps from the identity. The search anneals the 20 voltages on that
uncovered-count cost, updating two columns per move. The result has 4N vertices, so it beats the
parent's 3582 once N >= 1001. Only a graph that passes lib.is_valid is returned. Otherwise the
parent's valid Haar graph (3582 vertices) is returned, and then a trivial graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

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


# ------------------------------------------------------------------------ Haar fallback

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


# ------------------------------------------------------------------ 2x2 lift search

TARGET = (10, 5)
LO, HI = 1001, 1060       # N = |G|; the lift has 4N vertices, so 4N > 4000 needs N >= 1001
TEMP = 0.7
PATIENCE = 3000
NUM_GROUPS = 8


def bfs_uncovered(G, V, src):
    """Number of vertices not within distance 5 of src in the graph with neighbour table G (V rows)."""
    seen = np.zeros(V, dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(5):
        nb = G[frontier].ravel()
        nb = nb[~seen[nb]]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        seen[nb] = True
        frontier = nb
    return V - int(seen.sum())


def anneal(MT, inv, N, rng, deadline):
    """Search the 2x2x5 voltages for a diameter-5 lift. Returns S (2,2,5) with cost 0, or None."""
    V = 4 * N
    G = np.zeros((V, 10), dtype=np.int64)

    def set_dart(i, j, t, s):
        # A-class i, column block j: neighbour (2+j)N + x*s
        G[i * N:(i + 1) * N, 5 * j + t] = (2 + j) * N + MT[:, s]
        # B-class 2+j, column block i: neighbour i*N + y*s^{-1}
        G[(2 + j) * N:(3 + j) * N, 5 * i + t] = i * N + MT[:, int(inv[s])]

    def cost():
        return sum(bfs_uncovered(G, V, c * N) for c in range(4))

    while time.monotonic() < deadline:
        S = np.zeros((2, 2, 5), dtype=np.int64)
        for i in range(2):
            for j in range(2):
                S[i, j] = rng.choice(N, 5, replace=False)
                for t in range(5):
                    set_dart(i, j, t, int(S[i, j, t]))
        cur = cost()
        best_here = cur
        since = 0
        if cur == 0:
            return S
        while time.monotonic() < deadline:
            i = int(rng.integers(2))
            j = int(rng.integers(2))
            t = int(rng.integers(5))
            new = int(rng.integers(N))
            if new in S[i, j].tolist():
                continue
            oA = G[i * N:(i + 1) * N, 5 * j + t].copy()
            oB = G[(2 + j) * N:(3 + j) * N, 5 * i + t].copy()
            set_dart(i, j, t, new)
            c = cost()
            if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
                S[i, j, t] = new
                cur = c
                if cur == 0:
                    return S
                if cur < best_here:
                    best_here = cur
                    since = 0
            else:
                G[i * N:(i + 1) * N, 5 * j + t] = oA
                G[(2 + j) * N:(3 + j) * N, 5 * i + t] = oB
            since += 1
            if since > PATIENCE:
                break
    return None


def build_lift(MT, N, S):
    """Edge list of the 2x2 lift for voltages S (vertices: A_i = i*N + x, B_j = (2+j)*N + x)."""
    edges = []
    for i in range(2):
        for j in range(2):
            for t in range(5):
                s = int(S[i, j, t])
                A = i * N + np.arange(N)
                B = (2 + j) * N + MT[:, s].astype(np.int64)
                edges.extend(zip(A.tolist(), B.tolist()))
    return 4 * N, edges


def metacyclic_pool(lo, hi):
    """Specs (m, k, lam) for Z_m x|_lam Z_k with lo <= m*k <= hi, lam != 1, at most 2 lam per (m, k)."""
    out = []
    for k in range(2, 11):
        for m in range(2, hi // k + 1):
            if m * k < lo or m * k > hi:
                continue
            lams = []
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    lams.append(lam)
                    if len(lams) >= 2:
                        break
            for lam in lams:
                out.append((m, k, lam))
    return out


def run_bold(d, D, seed, time_limit, t0):
    """Try the 2x2 lift over several groups. Returns (n, edges) or None."""
    rng = np.random.default_rng(seed)
    deadline = t0 + 0.75 * time_limit
    pool = metacyclic_pool(LO, HI)
    if not pool:
        return None
    order = rng.permutation(len(pool))
    chosen = [pool[i] for i in order[:NUM_GROUPS]]
    for idx, (m, k, lam) in enumerate(chosen):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(chosen) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            N = m * k
            S = anneal(MT, inv, N, rng, slice_end)
        except Exception:
            continue
        if S is None:
            continue
        try:
            n, edges = build_lift(MT, N, S)
        except Exception:
            continue
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    try:
        res = run_bold(d, D, seed, time_limit, t0)
    except Exception:
        res = None
    if res is not None:
        return res
    # Safe fallback: the parent's valid Haar graph on 2*1791*... (3582 vertices).
    try:
        MT, _ = group_meta(199, 9, 180)
        g = checked(MT, [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
