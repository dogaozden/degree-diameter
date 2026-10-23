"""Haar-graph search over larger non-abelian groups for d=6, D=5 (numpy only).

CONSTRUCTION.  Take a finite group G of order N and a connection set S of 6 distinct elements.
Vertices A(g) = g and B(g) = N + g, with edges A(g) ~ B(s*g) for s in S.  This is a 6-regular
bipartite graph on 2N vertices.  Left multiplication by any h in G is an automorphism, so the
diameter is at most 5 iff BFS of radius 5 from A(e) and from B(e) reaches every vertex.

For N >= 343 the graph has 2N >= 686 > 684 vertices, which beats the record.  The search anneals S
with an exact BFS cost (number of unreached vertices).  Groups are tried in ascending order of order,
and once a valid graph is found, only strictly larger groups are searched.  Every result is checked
with lib.is_valid before it is returned.  If nothing is found, the valid order-660 Haar graph is
returned (also checked), and a trivial valid graph is the last resort.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_N = 343   # 2 * 343 = 686 > 684 (record)
MAX_N = 420
SLICE = 1.0   # seconds per anneal slice for one group
MAX_CANDS = 40


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
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
    """Group table from an (N, c) coordinate array (identity first) and a vectorised product."""
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


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------- candidate groups

def _candidates():
    """Groups with order in [MIN_N, MAX_N], sorted by order: metacyclic (non-abelian) and Heisenberg-type."""
    out = []
    for N in range(MIN_N, MAX_N + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lams = [lam for lam in range(2, m)
                    if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m]
            for lam in lams[:2]:
                out.append((N, ("meta", m, k, lam)))
    for p in (2, 3, 7):
        base = p ** 3
        for k in range(1, MAX_N // base + 1):
            N = base * k
            if MIN_N <= N <= MAX_N:
                out.append((N, ("heis", p, k)))
    out.sort(key=lambda t: t[0])
    return out[:MAX_CANDS]


def _make(spec):
    if spec[0] == "meta":
        return group_meta(spec[1], spec[2], spec[3])
    grp = group_heis(spec[1])
    return group_times_cyclic(grp, spec[2]) if spec[2] > 1 else grp


# ------------------------------------------------------------------------------- Haar cost and search

def _nbr(MT, inv, S, N):
    """Neighbour array (2N x DEG). A(g) ~ B(s*g) = N + MT[s, g]; B(g) ~ A(s^-1 * g) = MT[inv[s], g]."""
    return np.vstack([N + MT[S, :].T, MT[inv[S], :].T]).astype(np.int64)


def _cost(nbr, N):
    """Unreached vertices within DIAM steps from A(e) and from B(e) (0 means diameter <= DIAM)."""
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


def _anneal(MT, inv, N, deadline, rng):
    """Anneal the connection set until cost 0; return a checked (n, edges) or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost(_nbr(MT, inv, S, N), N)
        T = 1.0
        stall = 0
        while time.monotonic() < deadline and cur > 0 and stall < 3000:
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if x in S:
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = _cost(_nbr(MT, inv, newS, N), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
            T = max(0.2, T * 0.999)
        if cur == 0:
            nbr = _nbr(MT, inv, S, N)
            n = 2 * N
            edges = [(u, int(v)) for u in range(N) for v in nbr[u]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


# --------------------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        S = [0, 179, 116, 180, 47, 306]
        N = MT.shape[0]
        edges = [(int(a), int(N + MT[s, a])) for s in S for a in range(N)]
        if lib.is_valid(2 * N, edges, d, D):
            return 2 * N, edges
    except Exception:
        pass
    return trivial(d, D)


# --------------------------------------------------------------------------------------------- build

def _search_all(seed, time_limit):
    t0 = time.monotonic()
    budget = max(3.0, min(0.7 * time_limit, time_limit - 15.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = _candidates()
    tables = {}
    dead = set()
    best = None
    while time.monotonic() < deadline:
        active = False
        for idx, (N, spec) in enumerate(cands):
            if idx in dead:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            if best is not None and 2 * N <= best[0]:
                continue
            active = True
            if idx not in tables:
                try:
                    tables[idx] = _make(spec)
                except Exception:
                    dead.add(idx)
                    continue
            MT, inv = tables[idx]
            slice_end = min(deadline, now + SLICE)
            g = _anneal(MT, inv, N, slice_end, rng)
            if g is not None and (best is None or g[0] > best[0]):
                best = g
        if not active:
            break
    return best


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        best = _search_all(seed, time_limit)
    except Exception:
        best = None
    if best is not None:
        n, edges = best
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return _fallback(d, D)
