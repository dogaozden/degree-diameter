"""Bold variant for d=6, D=5: bipartite voltage lifts over small NON-abelian groups.

CONSTRUCTION.  Base graph: 4 base vertices A0, A1 (side A) and B0, B1 (side B), with 6 darts at every base
vertex.  Dart (p, q, g) joins (p, x) to (q, x*g) for all x in G.  The multiplicity matrix is
[[a, 6-a], [6-a, a]] for a random a in 1..5.  The lift has 4|G| vertices and is bipartite by construction.

WHY THE CHECK IS CHEAP.  Left multiplication by h maps (p, x) to (p, h*x) and preserves every edge, so it is an
automorphism.  Every vertex is therefore equivalent to (p, e) for its base vertex p.  The diameter is at most 5
iff the 4 sources (p, e) each reach all 4|G| vertices within 5 steps.  The search anneals voltages with that
uncovered-count cost, using a numpy BFS.

SAFETY.  Every candidate is rebuilt explicitly and checked with lib.is_valid.  A checked Haar graph of order 660
(the parent's valid fallback) is returned whenever no lift beats it.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- shared helpers

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


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


TARGET = (6, 5)
FALLBACK_S = [0, 179, 116, 180, 47, 306]   # valid Haar graph of order 330 in group_meta(33, 10, 26)


def fallback_graph(d, D):
    """Parent's checked Haar graph (order 660); trivial graph if anything goes wrong."""
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------------ voltage-lift search

SLICE = 1.5          # seconds per (group, attempt)
STALL_LIMIT = 3000   # moves without improvement before a random restart inside one attempt
PAIR_TEMP = 0.7


def lift_candidates(m):
    """All metacyclic groups Z_a x|_r Z_k of order m = a*k with a >= 2 (cyclic groups included via k = 1)."""
    out = []
    for k in range(1, m + 1):
        if m % k:
            continue
        a = m // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                out.append((m, a, k, r))
    return out


def group_table(a, k, r):
    """(order, MT, INV) as int64 numpy arrays for the semidirect product; identity is element 0."""
    order, mul, invf = lib.semidirect_group(a, k, r)
    MT = np.array([[mul(x, y) for y in range(order)] for x in range(order)], dtype=np.int64)
    INV = np.array([invf(x) for x in range(order)], dtype=np.int64)
    return order, MT, INV


def pair_pattern(A):
    """Base darts: row/column sums are 6 for the 2x2 multiplicity matrix [[A, 6-A], [6-A, A]]."""
    return ([(0, 2)] * A + [(0, 3)] * (6 - A)
            + [(1, 2)] * (6 - A) + [(1, 3)] * A)


def lift_cost(MT, INV, m, pairs, V):
    """Uncovered (source, vertex) pairs over the 4 base sources.  Zero means diameter <= 5."""
    N = 4 * m
    darts = [(p, q, int(g), int(INV[g])) for (p, q), g in zip(pairs, V)]
    total = 0
    for s in range(4):
        vis = np.zeros(N, dtype=bool)
        vis[s * m] = True          # identity of the group is element 0
        fr = vis.copy()
        for _ in range(5):
            nf = np.zeros(N, dtype=bool)
            for p, q, g, ig in darts:
                xs = np.flatnonzero(fr[p * m:(p + 1) * m])
                if xs.size:
                    nf[q * m + MT[xs, g]] = True
                ys = np.flatnonzero(fr[q * m:(q + 1) * m])
                if ys.size:
                    nf[p * m + MT[ys, ig]] = True
            nf &= ~vis
            if not nf.any():
                break
            vis |= nf
            fr = nf
        total += N - int(vis.sum())
    return total


def anneal(MT, INV, m, A, dl, rng):
    """Simulated annealing on the 12 voltages.  Returns (pairs, V) with cost 0, or None at the deadline."""
    pairs = pair_pattern(A)
    V = rng.integers(0, m, size=12)
    cur = lift_cost(MT, INV, m, pairs, V)
    stall = 0
    while True:
        if cur == 0:
            return pairs, V
        if time.monotonic() >= dl:
            return None
        t = int(rng.integers(12))
        old = int(V[t])
        V[t] = int(rng.integers(m))
        c = lift_cost(MT, INV, m, pairs, V)
        if c <= cur or rng.random() < math.exp(-(c - cur) / PAIR_TEMP):
            stall = 0 if c < cur else stall + 1
            cur = c
        else:
            V[t] = old
            stall += 1
        if stall > STALL_LIMIT:
            V = rng.integers(0, m, size=12)
            cur = lift_cost(MT, INV, m, pairs, V)
            stall = 0


def lift_edges(MT, m, pairs, V):
    """Explicit lift: base vertices 0,1 (side A) and 2,3 (side B); vertex (base, x) has id base*m + x."""
    edges = set()
    for (p, q), g in zip(pairs, V):
        g = int(g)
        for x in range(m):
            a = p * m + x
            b = q * m + int(MT[x, g])
            edges.add((min(a, b), max(a, b)))
    return 4 * m, sorted(edges)


# ------------------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)

    best = fallback_graph(d, D)
    best_n = best[0]

    pool = []
    for m in range(166, 200):          # 4m must exceed the parent's 660 (m >= 166)
        pool += lift_candidates(m)
    if not pool:
        return best
    order_idx = rng.permutation(len(pool))
    queue = [pool[i] for i in order_idx]

    qi = 0
    while time.monotonic() < end:
        m, a, k, r = queue[qi % len(queue)]
        qi += 1
        if 4 * m <= best_n:
            continue
        dl = min(end, time.monotonic() + SLICE)
        try:
            order, MT, INV = group_table(a, k, r)
            if order != m:
                continue
            A = int(rng.integers(1, 6))
            found = anneal(MT, INV, m, A, dl, rng)
        except Exception:
            continue
        if found is None:
            continue
        pairs, V = found
        try:
            n, edges = lift_edges(MT, m, pairs, V)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
        except Exception:
            pass
    return best
