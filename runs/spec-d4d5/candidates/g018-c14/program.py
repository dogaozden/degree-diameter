"""Bipartite (d, D) graphs by annealing edge switches on a biadjacency structure.

Strategy (replaces the parent's voltage-lift search):
  1. Safe fallback: K_{d,d} (valid for D >= 2) or the projective-plane incidence graph (D >= 3).
  2. Start from a Haar graph on h + h vertices (d random shifts, exactly d-regular, simple).
  3. Anneal over degree-preserving 2-switches (a,b),(c,e) -> (a,e),(c,b), which keep
     bipartiteness and degrees, minimising the number of vertex pairs at distance > D.
     The distance check uses boolean powers of M = I + A, so a cost evaluation is a few
     small dense matmuls.
  4. Grow h while annealing succeeds within its time chunk. Every candidate is checked with
     lib.is_valid before it replaces the best graph.
"""
import math
import random
import time

import numpy as np

import lib

_MAX_N = 400  # keep the dense matrix work bounded


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(M, D):
    """Number of unordered vertex pairs at distance > D (M is I + adjacency, float32)."""
    R = M
    for _ in range(D - 1):
        R = (R @ M > 0).astype(np.float32)
    zeros = R.size - int(np.count_nonzero(R))
    return zeros // 2


def _set(M, h, a, b, val):
    """Set the edge between left vertex a and right vertex b (stored as h + b) to val."""
    M[a, h + b] = val
    M[h + b, a] = val


def _search(d, D, h, rng, deadline):
    """Anneal a d-regular bipartite graph on h + h vertices; return edge list or None."""
    n = 2 * h
    M = np.eye(n, dtype=np.float32)
    shifts = rng.sample(range(h), d)
    edges = []  # [left, right] pairs, right index in 0..h-1
    for a in range(h):
        for s in shifts:
            b = (a + s) % h
            edges.append([a, b])
            _set(M, h, a, b, 1.0)
    cost = _cost(M, D)
    if cost == 0:
        return [(a, h + b) for a, b in edges]

    t_begin = time.monotonic()
    span = max(1e-3, deadline - t_begin)
    T0 = max(2.0, 0.02 * cost)
    T1 = 0.2
    T = T0
    E = len(edges)
    it = 0
    while cost > 0:
        it += 1
        if it % 32 == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = min(1.0, (now - t_begin) / span)
            T = T0 * (T1 / T0) ** frac
        i = rng.randrange(E)
        j = rng.randrange(E)
        if i == j:
            continue
        a, b = edges[i]
        c, e = edges[j]
        # Switch (a,b),(c,e) -> (a,e),(c,b); reject if it would repeat an edge or loop.
        if a == c or b == e or M[a, h + e] or M[c, h + b]:
            continue
        _set(M, h, a, b, 0.0)
        _set(M, h, c, e, 0.0)
        _set(M, h, a, e, 1.0)
        _set(M, h, c, b, 1.0)
        new = _cost(M, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            edges[i] = [a, e]
            edges[j] = [c, b]
        else:
            _set(M, h, a, e, 0.0)
            _set(M, h, c, b, 0.0)
            _set(M, h, a, b, 1.0)
            _set(M, h, c, e, 1.0)

    return [(a, h + b) for a, b in edges]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best_n, best_e = n0, [tuple(e) for e in e0]

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best_n, best_e = pg[0], [tuple(e) for e in pg[1]]

    # Annealed bipartite growth. Moore bound for the check below.
    if d >= 3 and D >= 3:
        bound = 2 * sum((d - 1) ** i for i in range(D))
        cap = min(bound, _MAX_N)
        last_ok = best_n // 2
        step = max(1, last_ok // 25)
        while time.monotonic() < deadline:
            h = last_ok + step
            if 2 * h > cap:
                break
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.2:
                break
            sub_deadline = now + min(remaining, max(0.4 * remaining, 2.0))
            edges_h = _search(d, D, h, rng, sub_deadline)
            if edges_h is None:
                if step == 1:
                    break
                step = max(1, step // 2)
                continue
            n = 2 * h
            if n > best_n and lib.is_valid(n, edges_h, d, D):
                best_n, best_e = n, edges_h
            last_ok = h

    if not lib.is_valid(best_n, best_e, d, D):
        return n0, [tuple(e) for e in e0]
    return best_n, best_e
