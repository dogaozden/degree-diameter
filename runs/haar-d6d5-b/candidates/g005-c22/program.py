"""Haar-graph search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

NEW IDEA IN THIS VERSION: exact word-coverage cost with identity normalisation.

For a Haar graph H(G, S) (A_g ~ B_{s g} for s in S, |S| = d) the diameter is at most 5 iff
    T = S^-1 S satisfies T*T = G   and   U = S S^-1 satisfies U*U = G.
This is an exact criterion (A-A and B-B distances are even words, A-B distances are odd words
S*T^k, and S*G = G).  Left-multiplying S by h leaves T unchanged and conjugates U, so we may
WLOG fix 1 in S.  The cost is then the number of uncovered elements of G in T*T plus those in U*U,
computed with two boolean-mask lookups on a d^2-size product table.  This is far cheaper than a
full BFS on the 2|G|-vertex graph, so many more moves are evaluated per second.

Moves: replace one free element of S by a random element, or by a product of two elements of S
(a word move that tends to fill gaps).  Simulated annealing with restarts, and round-robin time
slicing over several non-abelian groups of order 343..420 (Heisenberg mod 7 first, since its order
343 already beats the record of 684 vertices).

Every returned graph is checked with lib.is_valid.  Fallbacks: a checked order-660 Haar graph,
then K_{d,d} or a projective plane when they are valid.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5


# ------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, product (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
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


def _table_from_coords(elems, mulfun):
    """Table of a group given by coordinates (identity first) and a vectorised product."""
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
    e = np.array(list(itertools_product(p)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def itertools_product(p):
    return [(a, b, c) for a in range(p) for b in range(p) for c in range(p)]


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


# ------------------------------------------------------------------------- candidate groups

def _candidates():
    """Candidate groups with order in [343, 420] as (order, maker) pairs, smallest order first."""
    out = {}
    out[343] = [("heis", 7)]
    for N in range(343, 421):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.setdefault(N, []).append(("meta", m, k, lam))
                    break
    for k in (13, 14, 15):
        out.setdefault(27 * k, []).append(("heis3k", k))
    res = []
    for N in sorted(out):
        for c in out[N]:
            res.append((N, c))
    return res


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    if c[0] == "heis":
        return _finish(group_heis(c[1]))
    return group_times_cyclic(group_heis(3), c[1])


# -------------------------------------------------------------------------- cost and search

def _cover_cost(MT, inv, N, S):
    """Uncovered elements of T*T (T = S^-1 S) plus those of U*U (U = S S^-1).  0 means diameter <= 5."""
    iS = inv[S]
    T = np.unique(MT[iS[:, None], S[None, :]].ravel())
    m1 = np.zeros(N, dtype=bool)
    m1[MT[np.ix_(T, T)].ravel()] = True
    c1 = N - int(np.count_nonzero(m1))
    U = np.unique(MT[S[:, None], iS[None, :]].ravel())
    m2 = np.zeros(N, dtype=bool)
    m2[MT[np.ix_(U, U)].ravel()] = True
    c2 = N - int(np.count_nonzero(m2))
    return c1 + c2


def _anneal(MT, inv, N, deadline, rng):
    """Anneal S (with 0 in S) until cost 0 or the deadline; return S or None."""
    while time.monotonic() < deadline:
        S = np.empty(DEG, dtype=np.int64)
        S[0] = 0
        S[1:] = rng.choice(np.arange(1, N), size=DEG - 1, replace=False)
        cur = _cover_cost(MT, inv, N, S)
        T = 0.8
        stall = 0
        while cur > 0 and stall < 3000 and time.monotonic() < deadline:
            p = int(rng.integers(1, DEG))
            if rng.random() < 0.3:
                # word move: product of two current elements
                a, b = rng.integers(DEG, size=2)
                x = int(MT[S[a], S[b]])
            else:
                x = int(rng.integers(1, N))
            if x == 0 or np.any(S == x):
                stall += 1
                continue
            old = int(S[p])
            S[p] = x
            c = _cover_cost(MT, inv, N, S)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                stall = 0 if delta < 0 else stall + 1
            else:
                S[p] = old
                stall += 1
        if cur == 0:
            return S.copy()
    return None


def _haar_graph(MT, N, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    edges = []
    g = np.arange(N)
    for s in S:
        for a, b in zip(g, MT[int(s)]):
            edges.append((int(a), int(N + b)))
    return 2 * N, edges


# ------------------------------------------------------------------------------- fallbacks

def _trivial(d, D):
    """Small always-checked graphs for other (d, D)."""
    options = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        options.append(lambda: lib.projective_plane_incidence(d - 1))
    if d >= 1 and D >= 2:
        options.append(lambda: (2 * d, [(i, d + j) for i in range(d) for j in range(d)]))
    for make in options:
        try:
            n, e = make()
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
    return 2, [(0, 1)]


def _fallback(d, D):
    """Checked order-660 Haar graph for d=6, D=5, else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        n, e = _haar_graph(MT, 330, [0, 179, 116, 180, 47, 306])
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return _trivial(d, D)


# --------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _trivial(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    alive = _candidates()
    tables = {}
    best = None  # (N, graph)
    slice_t = 0.15

    while alive and time.monotonic() < deadline:
        for item in list(alive):
            N, c = item
            now = time.monotonic()
            if now >= deadline:
                break
            if best is not None and N <= best[0]:
                alive.remove(item)
                continue
            key = c
            if key not in tables:
                try:
                    tables[key] = _make(c)
                except Exception:
                    alive.remove(item)
                    continue
            MT, inv = tables[key]
            S = _anneal(MT, inv, N, min(deadline, now + slice_t), rng)
            if S is None:
                continue
            n, edges = _haar_graph(MT, N, S)
            if lib.is_valid(n, edges, d, D):
                best = (N, (n, edges))
                alive = [x for x in alive if x[0] > N]
        slice_t *= 2.0

    if best is not None:
        return best[1]
    return _fallback(d, D)
