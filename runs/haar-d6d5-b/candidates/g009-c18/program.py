"""Haar-graph search over metacyclic groups of order >= 342 for d=6, D=5 (numpy only).

CONSTRUCTION.  A Haar graph on a group G with a 6-element connection set S has vertices A_g, B_g (g in G) and
edges A_g ~ B_{s*g} for s in S.  It is bipartite, 6-regular, and has 2|G| vertices.  Its diameter is at most 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  So the search is over S, with cost = number of uncovered elements in
those two squared sets.  Only non-abelian metacyclic groups Z_m x|_r Z_k with order N in [342, 360] are tried.
N = 342 gives 684 vertices, which matches the record.  N >= 343 would beat it.

SEARCH.  Round-robin simulated annealing over the candidate groups, one replacement per move, with restarts.
Each group gets a time slice per round.  Any valid graph found is checked with lib.is_valid.  The largest valid
graph wins.  If nothing is found, the checked order-660 Haar graph is returned, or a trivial graph for other cases.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
N_LO = 342    # 2 * 342 = 684 (record)
N_HI = 360
STEPS_PER_RESTART = 6000
SLICE = 1.0   # seconds per task per round


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    if pow(lam, k, m) != 1 % m:
        raise ValueError("bad metacyclic parameters")
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


# ------------------------------------------------------------------------------- Haar helpers

def _to_graph(MT, S):
    """Haar graph: A-vertex g is g, B-vertex h is N + h, edges (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    edges = [(int(g), int(N + MT[s, g])) for s in S for g in range(N)]
    return 2 * N, edges


def _order(r, m):
    """Multiplicative order of r modulo m."""
    e, x = 1, r % m
    while x != 1 % m:
        x = (x * r) % m
        e += 1
    return e


def _tasks():
    """Candidate (m, k, r) metacyclic groups of order N in [N_LO, N_HI], at most 3 per order, largest r-order first."""
    out = []
    for N in range(N_LO, N_HI + 1):
        cands = []
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for r in range(2, m):
                if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                    continue
                if r % m == 1:
                    continue
                cands.append((_order(r, m), m, k, r))
        cands.sort(reverse=True)
        out += [(m, k, r) for _, m, k, r in cands[:3]]
    return out


# --------------------------------------------------------------------------------------- cost and search

def _cost(MT, inv, S):
    """Uncovered elements in (S^-1 S)^2 and (S S^-1)^2.  Cost 0 means the Haar graph has diameter <= 5."""
    N = MT.shape[0]
    iS = inv[S]
    total = 0
    for X, Y in ((iS, S), (S, iS)):
        D = MT[X[:, None], Y[None, :]].ravel().astype(np.int64)
        P = MT[D[:, None], D[None, :]].ravel()
        cov = np.zeros(N, dtype=bool)
        cov[P] = True
        total += N - int(np.count_nonzero(cov))
    return total


def _anneal(MT, inv, deadline, rng):
    """Simulated annealing with restarts until cost 0 or the deadline; returns S or None."""
    N = MT.shape[0]
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost(MT, inv, S)
        T = 2.0
        for _ in range(STEPS_PER_RESTART):
            if cur == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            p = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if x in S:
                continue
            S2 = S.copy()
            S2[p] = x
            c = _cost(MT, inv, S2)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = S2, c
            T = max(0.2, T * 0.9995)
        if cur == 0:
            return S
    return None


# ------------------------------------------------------------------------------------ fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        n, edges = _to_graph(MT, [0, 179, 116, 180, 47, 306])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    rng = np.random.default_rng(seed)
    tasks = _tasks()
    cache = {}
    done = set()
    best = None
    while time.monotonic() < deadline and len(done) < len(tasks):
        for idx, t in enumerate(tasks):
            if idx in done:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            try:
                if idx not in cache:
                    cache[idx] = group_meta(*t)
                MT, inv = cache[idx]
                S = _anneal(MT, inv, min(deadline, now + SLICE), rng)
            except Exception:
                done.add(idx)
                continue
            if S is not None:
                n, edges = _to_graph(MT, S)
                if lib.is_valid(n, edges, d, D):
                    if best is None or n > best[0]:
                        best = (n, edges)
                    done.add(idx)
    if best is not None:
        return best
    return _fallback(d, D)
