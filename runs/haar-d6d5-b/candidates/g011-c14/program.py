"""Haar-graph (two-orbit) search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

CONSTRUCTION.  Take a finite group G of order N >= 343 and a connection set S of 6 elements.
Vertices A(g) and B(g), g in G, with edges A(g) ~ B(s*g) for s in S.  The graph has 2N vertices,
is 6-regular and bipartite.  Right multiplication by any h in G is an automorphism that preserves
both sides, so the diameter is at most 5 iff BFS (radius 5) from A(e) and from B(e) reaches every
vertex.  Order 2N >= 686 beats the record 684.

Groups tried: the Heisenberg group mod 7 (order 343) first, then non-abelian metacyclic groups
Z_m x|_lam Z_k of orders 344..400.  Each group gets a slice of the time budget.  Search is simulated
annealing on S (one element replaced per move, with some moves taking a product of two generators),
with restarts when stuck.  A cost-0 set is checked with lib.is_valid before it is returned.  If no
group yields a valid graph, a valid order-660 Haar graph (checked) or a trivial graph is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
NMIN = 343   # 2 * 343 = 686 > 684 (record)


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
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


# ------------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D); the last resort is a single vertex."""
    options = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        options.append(lambda: lib.projective_plane_incidence(d - 1))
    options.append(lambda: lib.haar_graph(d, range(d)))
    for make in options:
        try:
            n, e = make()
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
    return 1, []


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        S = sorted({0, 179, 116, 180, 47, 306})
        N = MT.shape[0]
        edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
        n = 2 * N
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------- Haar graph and cost

def _nbr(MT, inv, N, S):
    """Neighbour array (2N x DEG).  A(g) = g, B(x) = N + x.  A(g) ~ B(s*g); B(x) ~ A(s^-1 * x)."""
    nbr = np.empty((2 * N, DEG), dtype=np.int64)
    nbr[:N] = N + MT[S].T
    nbr[N:] = MT[inv[S]].T
    return nbr


def _cost(nbr, N):
    """Vertices not reached within DIAM steps from A(e) and from B(e).  Zero means diameter <= DIAM."""
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


def _search(MT, inv, N, deadline, rng):
    """Anneal the connection set until cost 0; return a checked (n, edges) or None."""
    T = 0.6
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost(_nbr(MT, inv, N, S), N)
        stall = 0
        while cur > 0 and stall < 2500 and time.monotonic() < deadline:
            pos = int(rng.integers(DEG))
            if rng.random() < 0.3:
                i, j = (int(t) for t in rng.integers(DEG, size=2))
                x = int(MT[S[i], S[j]])
            else:
                x = int(rng.integers(N))
            if np.any(S == x):
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = _cost(_nbr(MT, inv, N, newS), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            nbr = _nbr(MT, inv, N, S)
            n = 2 * N
            edges = [(g, int(v)) for g in range(N) for v in nbr[g]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _candidates():
    """Heis(7) (order 343), then non-abelian metacyclic groups of orders 344..400, smallest first."""
    out = [("heis", 7)]
    for NN in range(NMIN, 401):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append(("meta", m, k, lam))
                    break
    return out[:14]


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    return group_heis(c[1])


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.7 * time_limit, time_limit - 15.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = _candidates()
    best = None
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = _make(c)
            N = MT.shape[0]
            g = _search(MT, inv, N, end, rng)
        except Exception:
            continue
        if g is not None and (best is None or g[0] > best[0]):
            best = g
    if best is not None:
        return best
    return _fallback(d, D)
