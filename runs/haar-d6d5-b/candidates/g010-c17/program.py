"""Haar-graph search over non-abelian metacyclic groups for the d=6, D=5 target (numpy only).

CONSTRUCTION.  A Haar graph on a group G of order N with connection set S (|S| = 6) has vertices A_g and B_g
(g in G) and edges A_g ~ B_{s*g} for s in S.  It is 6-regular and bipartite with 2N vertices.  Its diameter is at
most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G, so COST(S) = (N - |(S^-1 S)^2|) + (N - |(S S^-1)^2|) is 0 exactly
for valid S.  This replaces the earlier four-orbit bi-Cayley search, whose BFS cost was slow and found nothing.

SEARCH.  Candidate groups are metacyclic Z_m x| Z_k with orders 343..380, plus AGL(1,19) (order 342, which gives
the record 684).  Each candidate keeps its own annealing state.  Candidates are advanced round-robin in short
chunks, with restarts when stalled.  Any zero-cost S is verified with lib.is_valid before it is accepted.  A valid
graph on more than 684 vertices is returned immediately.  Otherwise the best valid graph found is returned at the
deadline.  If nothing is found, the checked valid order-660 Haar graph (or a trivial graph) is returned.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
RECORD_N = 684          # 2 * 342, the record
ANNEAL_T = 0.8
STALL_LIMIT = 3000
CHUNK = 200
MAX_CANDIDATES = 40


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


# ------------------------------------------------------------------------------- Haar helpers

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, edge (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    g = np.arange(N)
    edges = []
    for s in S:
        ys = MT[int(s)]
        edges.extend((int(a), int(N + b)) for a, b in zip(g, ys))
    return 2 * N, edges


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------------ cost and search

def cost(MT, inv, S, N):
    """(N - |(S^-1 S)^2|) + (N - |(S S^-1)^2|).  Zero iff the Haar graph on S has diameter <= 5."""
    Si = inv[S]
    P = np.unique(MT[Si[:, None], S[None, :]])
    Q = np.unique(MT[P[:, None], P[None, :]])
    R = np.unique(MT[S[:, None], Si[None, :]])
    Q2 = np.unique(MT[R[:, None], R[None, :]])
    return (N - Q.size) + (N - Q2.size)


def _restart(st, rng):
    st["S"] = rng.choice(st["N"], size=DEG, replace=False).astype(np.int64)
    st["cur"] = cost(st["MT"], st["inv"], st["S"], st["N"])
    st["stall"] = 0


def _advance(st, steps, rng, deadline):
    """Run up to `steps` annealing moves on one candidate state."""
    MT, inv, N = st["MT"], st["inv"], st["N"]
    for _ in range(steps):
        if st["cur"] == 0 or time.monotonic() > deadline:
            break
        S = st["S"]
        pos = int(rng.integers(DEG))
        x = int(rng.integers(N))
        if np.any(S == x):
            st["stall"] += 1
        else:
            newS = S.copy()
            newS[pos] = x
            c = cost(MT, inv, newS, N)
            delta = c - st["cur"]
            if delta <= 0 or rng.random() < math.exp(-delta / ANNEAL_T):
                st["S"], st["cur"] = newS, c
                st["stall"] = 0 if delta < 0 else st["stall"] + 1
            else:
                st["stall"] += 1
        if st["stall"] > STALL_LIMIT:
            _restart(st, rng)


def candidates():
    """Metacyclic groups Z_m x|_lam Z_k with order 343..380, plus AGL(1,19) (order 342) first."""
    out = [(19, 18, 2)]  # AGL(1,19): 2 is a primitive root mod 19
    for N in range(343, 381):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lams = [l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1]
            for l in lams[:2]:
                out.append((m, k, l))
    return out[:MAX_CANDIDATES]


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.7 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    states = []
    for (m, k, lam) in candidates():
        if time.monotonic() >= deadline:
            break
        try:
            MT, inv = group_meta(m, k, lam)
        except Exception:
            continue
        N = MT.shape[0]
        st = {"MT": MT, "inv": inv, "N": N, "S": None, "cur": None, "stall": 0}
        _restart(st, rng)
        states.append(st)

    best = None
    while states and time.monotonic() < deadline:
        for st in states:
            if time.monotonic() >= deadline:
                break
            _advance(st, CHUNK, rng, deadline)
            if st["cur"] == 0:
                try:
                    n, edges = haar_edges(st["MT"], st["S"])
                    if lib.is_valid(n, edges, DEG, DIAM):
                        if best is None or n > best[0]:
                            best = (n, edges)
                        if n > RECORD_N:
                            return best
                except Exception:
                    pass
                _restart(st, rng)

    if best is not None:
        return best
    return _fallback(d, D)
