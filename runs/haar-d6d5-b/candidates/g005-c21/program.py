"""Four-orbit lifted bipartite graphs for the d=6, D=5 target, with the Haar fallback kept as a safe default.

Construction: a base multigraph with 2 A-vertices (0, 1) and 2 B-vertices (2, 3). Blocks (A0,B0), (A1,B1)
get t darts each, and blocks (A0,B1), (A1,B0) get 6-t darts each, so every base vertex has degree 6. Each
dart (u, v, g) joins (u, x) to (v, x*g) for all x in a finite group G, giving a 6-regular bipartite graph on
4|G| vertices. Left multiplication by any h in G is an automorphism, so the diameter is at most 5 iff every
base vertex's identity fiber reaches all vertices within 5 steps. Voltages are annealed to minimise the number
of unreached (source, target) pairs. Groups are metacyclic Z_m x| Z_k with 4|G| > 660. Any result is checked
with lib.is_valid. If nothing is valid in time, a checked Haar graph of order 660 is returned.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)


def _trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback():
    """Haar graph on Z_33 x| Z_10 (order 330, 660 vertices), verified by lib.is_valid in build()."""
    N, mul, _ = lib.semidirect_group(33, 10, 26)
    S = [0, 179, 116, 180, 47, 306]
    edges = set()
    for s in S:
        for g in range(N):
            edges.add((g, N + mul(s, g)))
    return 2 * N, sorted(edges)


def _groups(lo, hi):
    """Metacyclic Z_m x| Z_k candidates (order m*k in [lo, hi]) given as (order, m, k, r)."""
    out = []
    for k in range(2, 9):
        for m in range(3, hi // k + 1):
            order = m * k
            if order < lo or order > hi:
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    out.append((order, m, k, r))
    return out


# Base blocks: (u, v) pairs; sizes are [t, 6-t, 6-t, t] for t in 1..5.
BLOCKS = [(0, 2), (0, 3), (1, 2), (1, 3)]


def _lift_edges(order, MT, vols):
    """Edges of the lift; vols[i] is the voltage list of BLOCKS[i]. Vertex (u, x) is u*order + x."""
    edges = set()
    for (u, v), volts in zip(BLOCKS, vols):
        for g in volts:
            for x in range(order):
                edges.add((u * order + x, v * order + MT[x][g]))
    return 4 * order, sorted(edges)


def _cost(order, edges, D):
    """Number of (identity-fiber source, target) pairs not within distance D. Zero iff the lift has diameter <= D."""
    n = 4 * order
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    total = 0
    for s in (0, order, 2 * order, 3 * order):
        dist = [-1] * n
        dist[s] = 0
        frontier = [s]
        for depth in range(1, D + 1):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = depth
                        nxt.append(v)
            frontier = nxt
            if not frontier:
                break
        total += dist.count(-1)
    return total


def _anneal(order, MT, rng, deadline, D=5):
    """Anneal voltages over random block sizes. Returns (best cost, voltage lists)."""
    best_c, best_v = 10 ** 9, None
    while time.monotonic() < deadline:
        t = int(rng.integers(1, 6))
        sizes = [t, 6 - t, 6 - t, t]
        vols = [[int(x) for x in rng.choice(order, size=s, replace=False)] for s in sizes]
        _, edges = _lift_edges(order, MT, vols)
        cur = _cost(order, edges, D)
        if cur < best_c:
            best_c, best_v = cur, [list(v) for v in vols]
        if cur == 0:
            return best_c, best_v
        temp = 0.8
        stall = 0
        while time.monotonic() < deadline and stall < 2500:
            i = int(rng.integers(4))
            p = int(rng.integers(len(vols[i])))
            new = int(rng.integers(order))
            if new in vols[i]:
                stall += 1
                continue
            old = vols[i][p]
            vols[i][p] = new
            _, edges = _lift_edges(order, MT, vols)
            c = _cost(order, edges, D)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = c
                stall = 0 if delta < 0 else stall + 1
                if cur < best_c:
                    best_c, best_v = cur, [list(v) for v in vols]
                if cur == 0:
                    return best_c, best_v
            else:
                vols[i][p] = old
                stall += 1
    return best_c, best_v


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
    rng = np.random.default_rng(seed)

    cands = _groups(166, 200)
    # Orders >= 172 first (they beat the record 684), then ascending; abelian (r = 1) last.
    cands.sort(key=lambda c: (c[0] < 172, c[0], c[3] == 1, float(rng.random())))

    for order, m, k, r in cands:
        now = time.monotonic()
        if now >= deadline:
            break
        try:
            order2, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        MT = [[mul(x, g) for g in range(order2)] for x in range(order2)]
        end = min(deadline, now + 6.0)
        try:
            bestc, vols = _anneal(order2, MT, rng, end)
        except Exception:
            continue
        if bestc == 0 and vols is not None:
            try:
                n, edges = _lift_edges(order2, MT, vols)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass

    try:
        n, edges = _fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return _trivial(d, D)
