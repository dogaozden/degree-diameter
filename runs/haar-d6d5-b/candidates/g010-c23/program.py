"""Haar-graph search on large non-abelian groups for the bipartite degree-diameter problem, d=6, D=5.

CONSTRUCTION.  Take a finite group G of order N and a connection set S of 6 group elements.  Vertices are
A_g = g and B_g = N + g.  Edges are A_g ~ B_{s*g} for s in S, so the graph is 6-regular, bipartite, and has
2N vertices.  Right multiplication by any h in G is an automorphism that preserves both sides, so the diameter is
at most 5 iff BFS of radius 5 from A_e and from B_e reaches every vertex.  COST(S) is the number of vertices not
reached from those two sources (0 means valid).

GROUPS.  Non-abelian groups are used because abelian groups waste most short words.  The candidates are the
Heisenberg group mod 7 (order 343) and metacyclic groups Z_m x|_lam Z_k with order 343..380 (these beat the record
684 = 2*342), plus a few metacyclic groups of order 331..342 as intermediate targets.

SEARCH.  Simulated annealing over S (one element replaced per move) runs round-robin over all candidate groups so
that no group gets all the time.  Restarts happen when a group stalls.  The first validated graph with 2N >= 686 is
returned at once.  Otherwise the largest validated graph is returned at the deadline.

SAFETY.  Every returned graph is checked with lib.is_valid.  If nothing valid is found, a checked order-660 Haar
graph is returned, and a trivial valid graph for other (d, D).
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
BEAT_N = 343          # 2 * 343 = 686 > 684 (record)
CHUNK = 0.8           # seconds of annealing per group per round
STALL_LIMIT = 20000   # non-improving steps before a restart


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


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    import itertools
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


# ------------------------------------------------------------------------------- Haar graph helpers

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def _nbr(MT, inv, N, S):
    """Neighbour array (2N x DEG): row g (A-vertex) lists N + s*g; row N+h (B-vertex) lists N + ... as A-indices."""
    nbr = np.empty((2 * N, DEG), dtype=np.int64)
    nbr[:N] = N + MT[S].T          # A_g ~ B_{s*g}
    nbr[N:] = MT[inv[S]].T         # B_h ~ A_{s^-1 * h}
    return nbr


def _cost(nbr, N):
    """Vertices not reached from A_e or B_e within DIAM steps (0 means diameter <= DIAM)."""
    n = 2 * N
    total = 0
    for src in (0, N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            nx = nbr[fr].ravel()
            nx = nx[~seen[nx]]
            if nx.size == 0:
                break
            nx = np.unique(nx)
            seen[nx] = True
            fr = nx
        total += n - int(np.count_nonzero(seen))
    return total


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


# ----------------------------------------------------------------------------- candidate groups

def _find_lam(m, k):
    """A multiplier lam (not 1) of order dividing k mod m, coprime to m, or None."""
    for lam in range(2, m):
        if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
            return lam
    return None


def _candidates():
    """Heis(7) (order 343) and non-abelian metacyclic groups: high orders first, then intermediate orders."""
    hi, lo = [("heis", 7, 0, 0)], []
    for N in range(BEAT_N, 381):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = _find_lam(m, k)
            if lam is not None:
                hi.append(("meta", m, k, lam))
    hi = hi[:8]
    for N in range(342, 330, -1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = _find_lam(m, k)
            if lam is not None:
                lo.append(("meta", m, k, lam))
    lo = lo[:4]
    return hi + lo


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    return group_heis(c[1])


# ------------------------------------------------------------------------------------ annealing

def _random_S(N, rng):
    return rng.choice(N, size=DEG, replace=False).astype(np.int64)


def _new_state(MT, inv, rng):
    N = MT.shape[0]
    S = _random_S(N, rng)
    return {"MT": MT, "inv": inv, "N": N, "rng": rng, "S": S,
            "cur": _cost(_nbr(MT, inv, N, S), N), "T": 1.0, "stall": 0, "done": False}


def _anneal(st, end):
    """Anneal S for this group until time `end`.  Returns a validated (n, edges) on success, else None."""
    MT, inv, N, rng = st["MT"], st["inv"], st["N"], st["rng"]
    S, cur = st["S"], st["cur"]
    while time.monotonic() < end:
        if cur == 0:
            break
        if st["stall"] > STALL_LIMIT:
            S = _random_S(N, rng)
            cur = _cost(_nbr(MT, inv, N, S), N)
            st["stall"] = 0
            continue
        pos = int(rng.integers(DEG))
        x = int(rng.integers(N))
        if np.any(S == x):
            st["stall"] += 1
            continue
        newS = S.copy()
        newS[pos] = x
        c = _cost(_nbr(MT, inv, N, newS), N)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / st["T"]):
            S, cur = newS, c
            st["stall"] = 0 if delta < 0 else st["stall"] + 1
        else:
            st["stall"] += 1
    st["S"], st["cur"] = S, cur
    if cur == 0:
        st["done"] = True
        n, edges = haar_edges(MT, S)
        if lib.is_valid(n, edges, DEG, DIAM):
            return n, edges
    return None


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.6 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    states = []
    for c in _candidates():
        if time.monotonic() > deadline - 1.0:
            break
        try:
            MT, inv = _make(c)
            states.append(_new_state(MT, inv, rng))
        except Exception:
            continue

    best = None
    while states and time.monotonic() < deadline:
        for st in states:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + CHUNK)
            try:
                g = _anneal(st, end)
            except Exception:
                st["done"] = True
                g = None
            if g is not None and (best is None or g[0] > best[0]):
                best = g
                if g[0] >= 2 * BEAT_N:
                    return best
        states = [s for s in states if not s["done"]]

    if best is not None:
        return best
    return _fallback(d, D)
