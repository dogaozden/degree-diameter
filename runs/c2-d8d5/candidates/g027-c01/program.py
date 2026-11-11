"""Abelian sumset (Haar-type) bipartite search.

Vertices: A = G and B = G for an abelian group G = Z_a x Z_b, with a_x ~ b_{x+s} for s in S, |S| = d.
The graph is bipartite and d-regular. Translation invariance means only two BFS runs (from a_0 and
from b_0) are needed to check diameter D. Simulated annealing moves elements of S to reduce the
number of unreached pairs. Exact projective-plane and Araujo-Lopez constructions are used for D = 3,
and K_{d,d} is the safe fallback.
"""
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions (used for D = 3; calibration cases return immediately).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Abelian group tables for G = Z_a x Z_b, element x = i*b + j.
# sub[s, k] = k - s and add[s, k] = k + s (as element indices).
# ----------------------------------------------------------------------------

def _tables(a, b):
    N = a * b
    x = np.arange(N, dtype=np.int64)
    xi, xj = x // b, x % b
    sub = (((xi[None, :] - xi[:, None]) % a) * b + (xj[None, :] - xj[:, None]) % b).astype(np.int32)
    add = (((xi[None, :] + xi[:, None]) % a) * b + (xj[None, :] + xj[:, None]) % b).astype(np.int32)
    return sub, add


def _pick_group(N, rng):
    """Return (a, b) with a * b = N. Cyclic groups are chosen about half the time."""
    divs = [b for b in range(1, N + 1) if N % b == 0]
    b = 1 if rng.random() < 0.5 else rng.choice(divs)
    return N // b, b


# ----------------------------------------------------------------------------
# Cost: number of unordered pairs at distance > D (counted with multiplicity
# that is zero exactly when the diameter is at most D).
# ----------------------------------------------------------------------------

def _bfs(N, tm, tn, D, src):
    """Visited sets [visA, visB] of BFS to depth D from vertex 0 on side src."""
    vis = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
    front = np.zeros(N, dtype=bool)
    front[0] = True
    vis[src][0] = True
    side = src
    for _ in range(D):
        tabs = tm if side == 0 else tn
        new = np.zeros(N, dtype=bool)
        for t in tabs:
            new |= front[t]
        new &= ~vis[1 - side]
        if not new.any():
            break
        vis[1 - side] |= new
        front = new
        side = 1 - side
    return vis


def _cost(N, sub, add, S, D):
    tm = [sub[s] for s in S]
    tn = [add[s] for s in S]
    va = _bfs(N, tm, tn, D, 0)
    vb = _bfs(N, tm, tn, D, 1)
    # A-A and A-B pairs from a_0; B-B pairs from b_0.
    return int(N - va[0].sum()) + int(N - va[1].sum()) + int(N - vb[1].sum())


def _anneal(N, d, D, sub, add, rng, deadline):
    """Search S (containing 0, size d) with zero cost. Returns S or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cost = _cost(N, sub, add, S, D)
    c0 = max(1.0, float(cost))
    best_c = cost
    last = 0
    iters = 0
    while cost > 0:
        iters += 1
        if (iters & 31) == 0 and time.monotonic() > deadline:
            break
        if iters - last > 4000:
            break
        temp = max(0.3, 0.03 * c0 * max(0.0, 1.0 - iters / 20000.0))
        i = rng.randrange(1, d)
        new = rng.randrange(N)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _cost(N, sub, add, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best_c:
                best_c = cost
                last = iters
        else:
            S[i] = old
    return S if cost == 0 else None


def _graph(N, add, S):
    """Edges a_x -- b_{x+s} for s in S; A is 0..N-1, B is N..2N-1."""
    edges = []
    for s in S:
        t = add[s]
        for x in range(N):
            edges.append((x, N + int(t[x])))
    return 2 * N, edges


def _sumset_search(best, d, D, rng, deadline, consider):
    """Repeatedly try to beat the current best order; returns the best graph found."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        N = max(d, best[0] // 2 + 1)
        if 2 * N > moore:
            break
        remaining = deadline - time.monotonic()
        slice_s = min(remaining, max(1.5, remaining / 3.0))
        a, b = _pick_group(N, rng)
        sub, add = _tables(a, b)
        S = _anneal(N, d, D, sub, add, rng, time.monotonic() + slice_s)
        if S is not None:
            n, edges = _graph(N, add, S)
            res = consider(n, edges)
            if res is not None:
                best = res
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, 0.85 * time_limit - 2.0)
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Return the new graph if it is a larger valid graph, else None."""
        if n > best[0] and lib.is_valid(n, e, d, D):
            return (n, e)
        return None

    # Exact constructions for D = 3.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            res = consider(pg[0], pg[1])
            if res is not None:
                best = res
            if lib.is_prime_power(d - 1):
                return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                res = consider(ar[0], ar[1])
                if res is not None:
                    best = res
            except (ValueError, RuntimeError):
                pass

    # Main construction: abelian sumset (Haar-type) search.
    if D >= 2 and d >= 2:
        best = _sumset_search(best, d, D, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
