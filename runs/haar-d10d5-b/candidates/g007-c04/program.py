"""Multi-orbit bi-Cayley search for the bipartite degree-diameter problem at diameter 5 (numpy only).

The parent searched single Haar graphs: one group G, one connection set S, 2|G| vertices. This version
uses a different construction for the target case: a bi-Cayley graph with K = 2 orbits on each side, so
4|G| vertices. Block sizes sz[i][j] (orbit A_i to orbit B_j) form a matrix with all row and column sums
equal to d. Vertices are (g, A_i) and (g, B_j); edges (g, A_i) ~ (s*g, B_j) for s in S[i][j].

The right-multiplication action g -> g*h is an automorphism that acts regularly on each orbit. So the
diameter is at most D iff a BFS of radius D from each of the 2K base vertices (1, X) reaches every vertex.
The cost is the total number of uncovered vertices over those 2K BFS runs, and cost 0 means valid.

Search: simulated annealing over the block elements, with random restarts. Every candidate is checked with
lib.is_valid before it is returned. If no valid multi-orbit graph is found, the parent's valid Haar graph
(order 1791, 3582 vertices) is used, and trivial() covers all other cases.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
K = 2             # orbits per side
TEMP = 1.0        # Metropolis temperature
PATIENCE = 3000   # non-improving moves before a restart


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j. Needs lam^k = 1 mod m."""
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
    """Table of a group given as an (N, c) integer coordinate array (identity first) and a vectorised product."""
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
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------- bi-Cayley graph and cost

def block_sizes(d, a):
    """Block sizes sz[i][j] with every row and column summing to d."""
    return [[a, d - a], [d - a, a]]


def build_nbr(MT, inv, S, N, d):
    """Adjacency (M x d) of the bi-Cayley graph. A_i vertex g is i*N+g; B_j vertex h is (K+j)*N+h."""
    M = 2 * K * N
    nbr = np.empty((M, d), dtype=np.int64)
    for i in range(K):
        c = 0
        for j in range(K):
            for s in S[i][j]:
                nbr[i * N:(i + 1) * N, c] = (K + j) * N + MT[s]
                c += 1
        if c != d:
            raise ValueError("row degree mismatch")
    for j in range(K):
        c = 0
        for i in range(K):
            for s in S[i][j]:
                nbr[(K + j) * N:(K + j + 1) * N, c] = i * N + MT[inv[s]]
                c += 1
        if c != d:
            raise ValueError("column degree mismatch")
    return nbr


def uncovered(nbr, N, D):
    """Total uncovered vertices from the 2K base vertices (1, X) within radius D. Zero means diameter <= D."""
    M = nbr.shape[0]
    total = 0
    for x in range(2 * K):
        src = x * N  # identity element of orbit x (identity has index 0)
        vis = np.zeros(M, dtype=bool)
        vis[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = nbr[fr].ravel()
            nb = np.unique(nb[~vis[nb]])
            if nb.size == 0:
                break
            vis[nb] = True
            fr = nb
        total += M - int(vis.sum())
    return total


def graph_from_nbr(nbr, N):
    """Edge list from the A-side rows (each edge appears once)."""
    A = K * N
    edges = [(v, int(w)) for v in range(A) for w in nbr[v]]
    return 2 * A, edges


def _copy(S):
    return [[a.copy() for a in row] for row in S]


# ------------------------------------------------------------------------------------------- search

def anneal(MT, inv, d, D, a, rng, deadline):
    """Anneal block elements until cost 0 or the deadline. Returns the zero-cost S, or None."""
    N = MT.shape[0]
    sz = block_sizes(d, a)
    blocks = [(i, j) for i in range(K) for j in range(K) if sz[i][j] > 0]

    def cost_of(S):
        return uncovered(build_nbr(MT, inv, S, N, d), N, D)

    best_S, best_c = None, None
    while time.monotonic() < deadline:
        S = [[rng.choice(N, sz[i][j], replace=False).astype(np.int64) for j in range(K)] for i in range(K)]
        cur = cost_of(S)
        if best_c is None or cur < best_c:
            best_S, best_c = _copy(S), cur
        since = 0
        while time.monotonic() < deadline and since < PATIENCE and cur > 0:
            i, j = blocks[int(rng.integers(len(blocks)))]
            p = int(rng.integers(sz[i][j]))
            x = int(rng.integers(N))
            if np.any(S[i][j] == x):
                continue
            old = S[i][j][p]
            S[i][j][p] = x
            c = cost_of(S)
            if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
                cur = c
                if cur < best_c:
                    best_S, best_c = _copy(S), cur
                    since = 0
                else:
                    since += 1
            else:
                S[i][j][p] = old
                since += 1
        if best_c == 0:
            break
    if best_S is not None and best_c == 0:
        return best_S
    return None


# ------------------------------------------------------------------------------- plan and fallback

def plan_groups():
    """(name, builder, block parameter a) entries: a metacyclic group of order about 1000, then other families."""
    plan = []
    for N in range(1000, 1101):
        for k in (3, 4, 5, 6, 2, 8, 9, 10):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = next((l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1 and l != 1), None)
            if lam is None:
                continue
            plan.append((f"Z{m}x|Z{k}", (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), 5))
            break
        if len(plan) >= 3:
            break
    plan += [
        ("SL(2,7)xZ3", lambda: group_times_cyclic(group_sl2(7), 3), 5),
        ("SL(2,5)xZ9", lambda: group_times_cyclic(group_sl2(5), 9), 5),
        ("Heis5xZ8", lambda: group_times_cyclic(group_heis(5), 8), 5),
    ]
    if plan:
        name, builder, _ = plan[0]
        plan.append((name + " a=4", builder, 4))
        plan.append((name + " a=6", builder, 6))
    return plan


def haar_edges(MT, S):
    """Edges of a Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def fallback_haar(d, D):
    """Parent's valid Haar graph (order 1791, 3582 vertices), or None if it fails the check."""
    try:
        MT, _ = group_meta(199, 9, 180)
        S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
        n, edges = haar_edges(MT, S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def solve(d, D, seed, time_limit):
    """Run the multi-orbit annealing over the plan and return the largest valid graph, or None."""
    t0 = time.monotonic()
    end_all = t0 + 0.7 * time_limit
    rng = np.random.default_rng(seed)
    best, best_n = None, 0
    plan = plan_groups()
    for idx, (name, builder, a) in enumerate(plan):
        now = time.monotonic()
        remaining = end_all - now
        if remaining <= 1.0:
            break
        end = now + remaining / (len(plan) - idx)
        try:
            MT, inv = builder()
            N = MT.shape[0]
            if not np.array_equal(MT[0], np.arange(N)):
                continue
            S = anneal(MT, inv, d, D, a, rng, end)
            if S is None:
                continue
            n, edges = graph_from_nbr(build_nbr(MT, inv, S, N, d), N)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best, best_n = (n, edges), n
        except Exception:
            continue
    return best


def build(d, D, seed, time_limit):
    try:
        if (d, D) != TARGET:
            return trivial(d, D)
        res = solve(d, D, seed, float(time_limit))
        if res is None:
            res = fallback_haar(d, D)
        if res is None:
            return trivial(d, D)
        return res
    except Exception:
        return trivial(d, D)
