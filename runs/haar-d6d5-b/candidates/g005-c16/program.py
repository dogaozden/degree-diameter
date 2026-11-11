"""Voltage lifts over small non-abelian groups for the d=6, D=5 target, with a safe validated fallback.

Construction: a 4-vertex bipartite base multigraph (A0, A1 | B0, B1), each vertex of degree 6, with
dart multiplicities [[t, 6-t], [6-t, t]] (t in {2,3,4}).  Its Z-lift over a metacyclic group G = Z_m x|_r Z_k
has 4|G| vertices, which beats the record 684 once |G| >= 172.  The 12 dart voltages are searched by
simulated annealing, with lib.bad_pairs as the cost (0 means diameter <= 5).  Any result is re-checked with
lib.is_valid before it is returned.  If the search fails, the proven 660-vertex Haar graph
(Z_33 x| Z_10, S = [0,179,116,180,47,306]) is returned instead.
"""
import math
import random
import time

import lib


TARGET = (6, 5)
FALLBACK_GROUP = (33, 10, 26)
FALLBACK_S = [0, 179, 116, 180, 47, 306]


def _trivial(d, D):
    """A small always-valid graph for any other (d, D)."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lib.projective_plane_incidence(d - 1))
    if D >= 2 and d >= 1:
        cands.append((2 * d, [(i, d + j) for i in range(d) for j in range(d)]))
    if D >= 1 and d >= 1:
        cands.append((2, [(0, 1)]))
    for n, e in cands:
        if lib.is_valid(n, e, d, D):
            return n, e
    return 1, []


def _fallback(d, D):
    """The proven 660-vertex Haar graph; re-checked before use."""
    try:
        m, k, lam = FALLBACK_GROUP
        N, mul, _ = lib.semidirect_group(m, k, lam)
        edges = [(g, N + mul(s, g)) for s in FALLBACK_S for g in range(N)]
        n = 2 * N
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return _trivial(d, D)


def _group_candidates(lo=172, hi=200):
    """Metacyclic groups Z_m x|_r Z_k (non-abelian r != 1) with order in [lo, hi], smallest first."""
    out = []
    for k in range(2, 9):
        for m in range(3, hi // k + 1):
            if m * k < lo or m * k > hi:
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            for r in rs[:3]:
                out.append((m * k, m, k, r))
    out.sort()
    return out


def _search(rng, cand, t, deadline):
    """Anneal the 12 dart voltages of the 4-vertex lift; return a checked graph or None."""
    _, m, k, r = cand
    order, mul, _ = lib.semidirect_group(m, k, r)
    pairs = ([(0, 2)] * t + [(0, 3)] * (6 - t) +
             [(1, 2)] * (6 - t) + [(1, 3)] * t)
    volts = [rng.randrange(order) for _ in pairs]

    def evaluate(v):
        darts = [(u, w, g) for (u, w), g in zip(pairs, v)]
        n, edges = lib.group_lift(4, darts, order, mul)
        return n, edges, lib.bad_pairs(n, edges, 5)

    n, edges, cur = evaluate(volts)
    stale = 0
    while time.monotonic() < deadline:
        if cur == 0:
            if lib.is_valid(n, edges, 6, 5):
                return n, edges
            return None
        i = rng.randrange(len(volts))
        old = volts[i]
        volts[i] = rng.randrange(order)
        n2, e2, c2 = evaluate(volts)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / 2.0):
            cur, n, edges = c2, n2, e2
            stale = 0 if delta < 0 else stale + 1
        else:
            volts[i] = old
            stale += 1
        if stale > 2000:
            return None
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _trivial(d, D)
    deadline = time.monotonic() + 0.8 * time_limit
    fb = _fallback(d, D)
    rng = random.Random(seed)
    try:
        cands = _group_candidates()
        if not cands:
            return fb
        while time.monotonic() < deadline - 0.5:
            cand = rng.choice(cands)
            t = rng.choice([2, 3, 4])
            res = _search(rng, cand, t, deadline)
            if res is not None:
                n, edges = res
                if n > fb[0] and lib.is_valid(n, edges, d, D):
                    return n, edges
    except Exception:
        pass
    return fb
