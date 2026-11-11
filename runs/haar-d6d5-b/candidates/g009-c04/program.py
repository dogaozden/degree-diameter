"""Bi-Cayley and Haar search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

CONSTRUCTION 1 (bi-Cayley).  Take a finite group G of order N and four connection sets S_ij of sizes
a, 6-a, 6-a, a, so every vertex has degree 6.  Vertices are A_i(g) and B_j(g) for g in G, with edges
A_i(g) ~ B_j(g*s) for s in S_ij.  Left multiplication is an automorphism, so the diameter is at most 5 iff
BFS of radius 5 from the four base vertices reaches everything.  The graph has 4N vertices.

CONSTRUCTION 2 (Haar).  Vertices (g, A) and (g, B), edges (g, A) ~ (s*g, B) for s in S, |S| = 6.  This has
2N vertices.  Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G, so the cost is the number of
uncovered group elements.  Evaluating this cost is cheap (about 36 products per set), so annealing is fast.

Phase 1 runs the bi-Cayley search for a share of the budget.  If it finds nothing, phase 2 anneals Haar sets
over non-abelian metacyclic groups of order 331..342 (graphs with 662..684 vertices, which beat 660).  Every
result is checked with lib.is_valid.  If nothing is found, the valid order-660 Haar graph (or a trivial graph)
is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_N = 172   # bi-Cayley: 4 * 172 = 688 > 684 (record)
HAAR_LO, HAAR_HI = 331, 342   # Haar: 2N = 662..684


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


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------- Haar fallback helpers

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


# ------------------------------------------------------------------------- Haar search (phase 2)

def _haar_cost(MT, inv, S):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2 in G (0 means diameter <= 5)."""
    N = MT.shape[0]
    iS = inv[S]
    P = np.unique(MT[iS[:, None], S[None, :]])
    Q = np.unique(MT[S[:, None], iS[None, :]])
    P2 = np.unique(MT[P[:, None], P[None, :]])
    Q2 = np.unique(MT[Q[:, None], Q[None, :]])
    return 2 * N - P2.size - Q2.size


def _haar_search(MT, inv, deadline, rng):
    """Anneal a 6-element set S until the Haar cost is 0; return a checked (n, edges) or None."""
    N = MT.shape[0]
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _haar_cost(MT, inv, S)
        T = 1.0
        stall = 0
        while time.monotonic() < deadline and cur > 0 and stall < 3000:
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if np.any(S == x):
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = _haar_cost(MT, inv, newS)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            n, edges = haar_edges(MT, S.tolist())
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _haar_candidates():
    """Non-abelian metacyclic groups with order in [HAAR_LO, HAAR_HI], largest order first."""
    out = []
    for NN in range(HAAR_HI, HAAR_LO - 1, -1):
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
    return out[:10]


# ------------------------------------------------------------------------- bi-Cayley graph and cost

def _nbr(MT, inv, N, S):
    """Neighbour array (4N x DEG).  Orbits: A_0 = 0..N-1, A_1 = N..2N-1, B_0 = 2N..3N-1, B_1 = 3N..4N-1.
    A_i(g) ~ B_j(g*s) for s in S[(i, j)]."""
    g = np.arange(N, dtype=np.int64)
    nbr = np.empty((4 * N, DEG), dtype=np.int64)
    for i in (0, 1):
        c = 0
        for j in (0, 1):
            for s in S[(i, j)]:
                nbr[i * N:(i + 1) * N, c] = (2 + j) * N + MT[g, s]
                c += 1
    for j in (0, 1):
        c = 0
        for i in (0, 1):
            for s in S[(i, j)]:
                nbr[(2 + j) * N:(3 + j) * N, c] = i * N + MT[g, inv[s]]
                c += 1
    return nbr


def _cost(nbr, N):
    """Vertices not reached within DIAM steps from the four base vertices (0 means diameter <= DIAM)."""
    n = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            nx = nbr[fr].ravel()
            nx = np.unique(nx[~seen[nx]])
            if nx.size == 0:
                break
            seen[nx] = True
            fr = nx
        total += n - int(np.count_nonzero(seen))
    return total


def _search(MT, inv, N, deadline, rng):
    """Anneal the four connection sets until cost 0; return a checked (n, edges) or None."""
    while time.monotonic() < deadline:
        a = int(rng.choice([2, 3, 3, 4]))
        sizes = {(0, 0): a, (0, 1): DEG - a, (1, 0): DEG - a, (1, 1): a}
        keys = list(sizes)
        S = {k: rng.choice(N, size=sizes[k], replace=False).astype(np.int64) for k in keys}
        cur = _cost(_nbr(MT, inv, N, S), N)
        stall = 0
        T = 0.6
        while time.monotonic() < deadline and cur > 0 and stall < 4000:
            key = keys[int(rng.integers(4))]
            pos = int(rng.integers(sizes[key]))
            x = int(rng.integers(N))
            if x in S[key]:
                stall += 1
                continue
            newS = dict(S)
            arr = S[key].copy()
            arr[pos] = x
            newS[key] = arr
            c = _cost(_nbr(MT, inv, N, newS), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            nbr = _nbr(MT, inv, N, S)
            n = 4 * N
            edges = [(u, int(v)) for u in range(2 * N) for v in nbr[u]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _candidates():
    """Non-abelian metacyclic groups of order in [MIN_N, 200], plus Heis(3) x Z_7 (order 189)."""
    out = []
    for NN in range(MIN_N, 201):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and pow(lam, 1, m) != 1:
                    out.append(("meta", m, k, lam))
                    break
    out = out[:8]
    out.append(("heis", 3, 7, 0))
    return out


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    return group_times_cyclic(group_heis(c[1]), c[2])


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    split = t0 + 0.4 * budget          # phase 1 (bi-Cayley) share
    rng = np.random.default_rng(seed)

    best = None

    # Phase 1: bi-Cayley graphs (4N vertices, N >= 172 beats the record).
    cands = _candidates()
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= split:
            break
        end = now + (split - now) / (len(cands) - idx)
        try:
            MT, inv = _make(c)
            N = MT.shape[0]
            g = _search(MT, inv, N, end, rng)
        except Exception:
            continue
        if g is not None and (best is None or g[0] > best[0]):
            best = g

    # Phase 2: Haar graphs on groups of order 331..342 (2N vertices, beats 660), only if phase 1 failed.
    if best is None:
        hc = _haar_candidates()
        for idx, c in enumerate(hc):
            now = time.monotonic()
            if now >= deadline:
                break
            end = now + (deadline - now) / (len(hc) - idx)
            try:
                MT, inv = _make(c)
                g = _haar_search(MT, inv, end, rng)
            except Exception:
                continue
            if g is not None and (best is None or g[0] > best[0]):
                best = g
                break

    if best is not None:
        return best
    return _fallback(d, D)
