"""Voltage-lift search for the bipartite degree-diameter problem at diameter 5 (numpy only).

CONSTRUCTION.  Choose a finite group G of order N, a base of k A-vertices and k B-vertices, and DEG = 6
permutation layers sigma_r (r = 0..5), each a bijection A -> B.  Give every (layer r, A-vertex i) a voltage
g_{r,i} in G.  The lift has vertices (A, i, x) and (B, j, y) and edges (A, i, x) ~ (B, sigma_r(i), x * g_{r,i}).
Every vertex has degree 6 when no two layers produce the same edge (checked as a penalty).

The lift is invariant under left multiplication by G, so the distance between any two vertices reduces to
distances from the 2k base-vertex sources (u, e).  Cost = total number of vertices not reached within D = 5
steps from those sources, plus a large penalty for duplicate edges.  Cost 0 gives a valid graph.  Search is
simulated annealing over voltages and layer swaps, with restarts.  Every result is verified with lib.is_valid.
A precomputed valid Haar graph is the fallback.
"""
import math
import time

import numpy as np

import lib


DEG = 6
DIAM = 5
TARGET = (6, 5)


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
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


def metacyclic_catalogue(lo, hi, max_k=12, per_order=2):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with order in [lo, hi]: list of (order, m, k, lam)."""
    by_order = {}
    for k in range(2, max_k + 1):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            N = m * k
            if N < lo or N > hi:
                continue
            found = 0
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                by_order.setdefault(N, []).append((m, k, lam))
                found += 1
                if found >= per_order:
                    break
    cat = []
    for N in sorted(by_order):
        cat.extend((N, m, k, lam) for m, k, lam in by_order[N][:per_order])
    return cat


# ------------------------------------------------------------------------------- lift model and cost

def lift_nbr(MT, inv, k, perms, volt):
    """Neighbour array (n, DEG) of the lift.  A-vertex (i, x) = i*N + x, B-vertex (j, y) = (k+j)*N + y."""
    N = MT.shape[0]
    n = 2 * k * N
    nbr = np.empty((n, DEG), dtype=np.int64)
    x = np.arange(N)
    for r in range(DEG):
        for i in range(k):
            j = int(perms[r, i])
            g = int(volt[r, i])
            nbr[i * N:(i + 1) * N, r] = (k + j) * N + MT[x, g]
            nbr[(k + j) * N:(k + j + 1) * N, r] = i * N + MT[x, inv[g]]
    return n, nbr


def reach_cost(nbr, sources, n, D):
    """Total number of vertices NOT within distance D of each source (summed over sources)."""
    total = 0
    for s in sources:
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        frontier = np.array([s], dtype=np.int64)
        cnt = 1
        for _ in range(D):
            nxt = nbr[frontier].ravel()
            nxt = nxt[~seen[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            seen[nxt] = True
            cnt += int(nxt.size)
            frontier = nxt
        total += n - cnt
    return total


def evaluate(MT, inv, k, perms, volt, sources):
    """Cost (0 = valid up to verification), the vertex count and the neighbour array."""
    dup = 0
    for i in range(k):
        dup += DEG - len(set(zip(perms[:, i].tolist(), volt[:, i].tolist())))
    n, nbr = lift_nbr(MT, inv, k, perms, volt)
    c = reach_cost(nbr, sources, n, DIAM) + 1000 * dup
    return c, n, nbr


def anneal(MT, inv, k, deadline, rng, patience=2500, T=0.6):
    """Annealing with restarts.  Returns (perms, volt) of a cost-0 lift, or None at the deadline."""
    N = MT.shape[0]
    sources = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
    while time.monotonic() < deadline:
        perms = np.array([rng.permutation(k) for _ in range(DEG)], dtype=np.int64)
        volt = rng.integers(0, N, size=(DEG, k)).astype(np.int64)
        cur, _, _ = evaluate(MT, inv, k, perms, volt, sources)
        if cur == 0:
            return perms, volt
        bestc, since = cur, 0
        while since < patience:
            if time.monotonic() >= deadline:
                return None
            p2, v2 = perms.copy(), volt.copy()
            r = int(rng.integers(DEG))
            if rng.random() < 0.7:
                i = int(rng.integers(k))
                v2[r, i] = int(rng.integers(N))
            else:
                a, b = rng.choice(k, 2, replace=False)
                p2[r, a], p2[r, b] = p2[r, b], p2[r, a]
            c2, _, _ = evaluate(MT, inv, k, p2, v2, sources)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                perms, volt, cur = p2, v2, c2
                if cur == 0:
                    return perms, volt
                if cur < bestc:
                    bestc, since = cur, 0
                    continue
            since += 1
    return None


def to_graph(MT, inv, k, perms, volt, d, D):
    """Verified (n, edges) for the lift, or None."""
    N = MT.shape[0]
    n, nbr = lift_nbr(MT, inv, k, perms, volt)
    A = k * N
    edges = [(int(u), int(v)) for u in range(A) for v in nbr[u]]
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


# ------------------------------------------------------------------------------ fallback and trivial

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked_haar(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# --------------------------------------------------------------------------------------- sweep

def sweep(d, D, seed, time_limit):
    """Try lifts over many groups, in ascending order of vertex count, with adaptive time slices."""
    t0 = time.monotonic()
    deadline = t0 + 0.70 * time_limit
    rng = np.random.default_rng(seed)

    items = []  # (vertex count, base size k, group builder)
    cat_cache = {}
    for k in range(2, 7):
        lo = -(-661 // (2 * k))
        hi = 800 // (2 * k)
        for N in range(lo, hi + 1):
            if N not in cat_cache:
                cat_cache[N] = metacyclic_catalogue(N, N, per_order=1)
            for _, m, kk, lam in cat_cache[N]:
                items.append((2 * k * N, k, (lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam))))
            items.append((2 * k * N, k, (lambda N=N: group_meta(N, 1, 1))))
    items.sort(key=lambda t: t[0])

    best, best_n = None, 0
    for idx, (n_, k, builder) in enumerate(items):
        now = time.monotonic()
        if now >= deadline:
            break
        if n_ <= best_n:
            continue
        left = len(items) - idx
        slice_ = min(3.0, max(0.5, (deadline - now) / left))
        try:
            MT, inv = builder()
            res = anneal(MT, inv, k, now + slice_, rng)
            if res is None:
                continue
            g = to_graph(MT, inv, k, res[0], res[1], d, D)
        except Exception:
            continue
        if g is not None and g[0] > best_n:
            best, best_n = g, g[0]
    return best


# ============================================================================================= build

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    g = None
    try:
        g = sweep(d, D, seed, time_limit)
    except Exception:
        g = None
    if g is not None:
        return g
    try:
        MT, inv = FALLBACK[0]()
        g = checked_haar(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
