"""Two-orbit voltage lifts for the bipartite degree-diameter problem (d = 10, D = 5), numpy only.

NEW CONSTRUCTION.  The previous program used Haar graphs: one vertex orbit per side of a group G, joined by a
connection set S, so the order is 2|G|.  Here each side has k = 2 vertex orbits, so the order is 4|G|.
Orbit A_i has vertices (g, A_i) and orbit B_j has vertices (g, B_j), for g in G.  A dart (i, j, s) joins
(g, A_i) to (s*g, B_j) for every g.  Each A-orbit carries 10 darts in total and each B-orbit carries 10 darts,
so the graph is bipartite and 10-regular.  The darts are given by a 2x2 count matrix C with row and column sums 10.

WHY THE DIAMETER IS EASY TO CHECK.  Right multiplication by any h in G is an automorphism of every such lift.
So the diameter is the largest eccentricity of the 2k base vertices (1, X).  COST(darts) is the number of vertices
at distance > 5 from those base vertices, summed over them.  Cost 0 means diameter <= 5.

SEARCH.  Each dart's group element is a state variable.  Simulated annealing changes one dart at a time.  Restarts
happen when progress stalls.  Candidate groups are non-abelian metacyclic groups Z_a x| Z_b of order N, one per N,
tried in increasing N starting at 896 (so the order 4N exceeds the 3582-vertex fallback).

SAFETY.  Every cost-0 lift is built and checked with lib.is_valid before it is kept.  A validated Haar fallback of
order 3582 is always available.  Other (d, D) cases get a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


DEG = 10            # target degree
D_T = 5             # target diameter
TARGET = (10, 5)
TIME_FRAC = 0.72    # fraction of time_limit used for search (leaves a wide safety margin)
SLICE = 5.0         # seconds per candidate group
PATIENCE = 1500     # non-improving annealing steps before a restart
TEMP = 1.2
# 2x2 dart-count matrices: row i = A-orbit, column j = B-orbit.  Every row and column sums to DEG.
CS = [
    [[5, 5], [5, 5]],
    [[6, 4], [4, 6]],
    [[7, 3], [3, 7]],
]


# ----------------------------------------------------------------------------------------- group tables

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).
    Returns (multiplication table MT, inverse array inv); element 0 is the identity.  Needs lam^k = 1 mod m."""
    if pow(lam, k, m) != 1 % m:
        raise ValueError("lam^k must be 1 mod m")
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int64)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


# ------------------------------------------------------------------------------------- lift machinery

def slots_from_C(C):
    """Dart slots: slot t joins A-orbit I[t] to B-orbit J[t]; the group element of each slot is searched."""
    k = len(C)
    if any(sum(row) != DEG for row in C) or any(sum(C[i][j] for i in range(k)) != DEG for j in range(k)):
        raise ValueError("C must have all row and column sums equal to DEG")
    I, J = [], []
    for i, row in enumerate(C):
        for j, c in enumerate(row):
            I.extend([i] * c)
            J.extend([j] * c)
    return np.array(I, dtype=np.int64), np.array(J, dtype=np.int64)


def lift_nbr(MT, inv, k, I, J, S):
    """Neighbour table (n x DEG) of the lift.  Vertex ids: A-orbit i, element g -> i*G + g;
    B-orbit j, element h -> k*G + j*G + h."""
    G = MT.shape[0]
    n = 2 * k * G
    ar = np.arange(G, dtype=np.int64)
    nbr = np.empty((n, DEG), dtype=np.int64)
    for i in range(k):
        sa = np.flatnonzero(I == i)
        vals = MT[S[sa][None, :], ar[:, None]]                    # s * g
        nbr[i * G:(i + 1) * G] = k * G + J[sa][None, :] * G + vals
    for j in range(k):
        sb = np.flatnonzero(J == j)
        vals = MT[inv[S[sb]][None, :], ar[:, None]]               # s^-1 * h
        nbr[k * G + j * G:k * G + (j + 1) * G] = I[sb][None, :] * G + vals
    return nbr


def unreached(nbr, src, rad):
    """Number of vertices at distance > rad from src."""
    n = nbr.shape[0]
    seen = np.zeros(n, dtype=bool)
    seen[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(rad):
        m = np.zeros(n, dtype=bool)
        m[nbr[front].ravel()] = True
        m &= ~seen
        front = np.flatnonzero(m)
        if front.size == 0:
            break
        seen |= m
    return n - int(seen.sum())


def cost_of(nbr, srcs):
    """Total number of vertices beyond distance D_T from the base sources.  Zero means diameter <= D_T."""
    return sum(unreached(nbr, s, D_T) for s in srcs)


def edges_of(nbr):
    n = nbr.shape[0]
    src = np.repeat(np.arange(n, dtype=np.int64), DEG)
    dst = nbr.ravel()
    m = src < dst
    return n, list(zip(src[m].tolist(), dst[m].tolist()))


def random_S(groups, T, G, rng):
    S = np.zeros(T, dtype=np.int64)
    for idx in groups.values():
        S[idx] = rng.choice(G, size=len(idx), replace=False)
    return S


def anneal(MT, inv, I, J, groups, gid, srcs, rng, end, k, S):
    """Simulated annealing over dart elements.  Returns a cost-0 dart assignment, or None at the deadline."""
    G = MT.shape[0]
    T = len(S)

    def f(X):
        return cost_of(lift_nbr(MT, inv, k, I, J, X), srcs)

    cur = f(S)
    best = cur
    since = 0
    while cur > 0:
        if time.monotonic() >= end:
            return None
        t = int(rng.integers(T))
        idx = groups[gid[t]]
        others = {int(S[u]) for u in idx if u != t}      # keep darts into one orbit pair distinct
        x = int(rng.integers(G))
        while x in others:
            x = int(rng.integers(G))
        old = int(S[t])
        S[t] = x
        c2 = f(S)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            cur = c2
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            S[t] = old
            since += 1
        if since > PATIENCE:
            S = random_S(groups, T, G, rng)
            cur = f(S)
            best, since = cur, 0
    return S


def candidates():
    """One group per order N in 896..1000: a non-abelian Z_a x| Z_b of order N if one exists, else cyclic Z_N."""
    out = []
    for N in range(896, 1001):
        found = None
        bs = [b for b in range(3, N) if N % b == 0] + ([2] if N % 2 == 0 else [])
        for b in bs:
            a = N // b
            if a < 3:
                continue
            for lam in range(2, a):
                if math.gcd(lam, a) == 1 and pow(lam, b, a) == 1:
                    found = (a, b, lam)
                    break
            if found:
                break
        if found is None:
            found = (N, 1, 1)
        out.append((N,) + found)
    return out


def try_order(a, b, lam, C, rng, end):
    """Search darts for the group Z_a x| Z_b (order a*b) and count matrix C.  Returns a validated (n, edges)
    or None."""
    MT, inv = group_meta(a, b, lam)
    G = MT.shape[0]
    k = len(C)
    I, J = slots_from_C(C)
    T = len(I)
    groups = {}
    for t in range(T):
        groups.setdefault((int(I[t]), int(J[t])), []).append(t)
    groups = {key: np.array(v, dtype=np.int64) for key, v in groups.items()}
    gid = [(int(I[t]), int(J[t])) for t in range(T)]
    srcs = [X * G for X in range(2 * k)]
    while time.monotonic() < end:
        S = random_S(groups, T, G, rng)
        S = anneal(MT, inv, I, J, groups, gid, srcs, rng, end, k, S)
        if S is None:
            return None
        n, edges = edges_of(lift_nbr(MT, inv, k, I, J, S))
        if lib.is_valid(n, edges, DEG, D_T):
            return n, edges
        return None
    return None


# ----------------------------------------------------------------------------------- fallbacks

def haar(MT, S):
    """Haar graph: (g, A) ~ (s*g, B) for s in S.  A-vertex g is g, B-vertex g is G + g."""
    G = MT.shape[0]
    g = list(range(G))
    edges = []
    for s in sorted({int(x) for x in S}):
        row = MT[s].tolist()
        edges.extend((g_, G + row[g_]) for g_ in g)
    return 2 * G, edges


def fallback():
    """Validated Haar graph of order 3582 (checked at run time), or None."""
    try:
        MT, _ = group_meta(199, 9, 180)
        n, edges = haar(MT, [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])
        if lib.is_valid(n, edges, DEG, D_T):
            return n, edges
    except Exception:
        pass
    return None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget_end = t0 + TIME_FRAC * time_limit
    rng = np.random.default_rng(seed)

    best = fallback()
    best_n = best[0] if best is not None else 0

    for idx, (N, a, b, lam) in enumerate(candidates()):
        now = time.monotonic()
        if now >= budget_end - 0.5:
            break
        if 4 * N <= best_n:
            continue
        C = CS[idx % len(CS)]
        try:
            res = try_order(a, b, lam, C, rng, min(budget_end, now + SLICE))
        except Exception:
            res = None
        if res is not None and res[0] > best_n:
            best, best_n = res, res[0]

    if best is not None:
        return best
    return trivial(d, D)
