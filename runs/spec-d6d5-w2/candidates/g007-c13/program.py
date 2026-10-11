"""Degree-preserving growth of bipartite graphs with switch annealing.

Start from K_{d,d} (diameter 2). Repeatedly splice in one new left and one new
right vertex of degree d (this keeps every old degree), then repair the diameter
with random 2-switches that keep the graph simple and bipartite. The objective is
the number of ordered vertex pairs at distance > D, computed with bitmask BFS in
numpy. Algebraic baselines (K_{d,d}, PG(2,q) incidence, Araujo-Pardo-Lopez, cycles
for d = 2) are checked with lib.is_valid and used as the fallback.
"""
import math
import random
import time

import numpy as np

import lib

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _baseline(d, D):
    """Largest valid algebraic graph among a few known constructions."""
    cands = [lib.haar_graph(d, range(d))]  # K_{d,d}, diameter 2
    if d == 2 and D >= 2:
        m = 2 * D
        cands.append((m, [(i, (i + 1) % m) for i in range(m)]))
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        cands.append(lib.projective_plane_incidence(d - 1))
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    best = None
    for n, e in cands:
        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
            best = (n, e)
    if best is None:
        best = lib.haar_graph(d, range(d))
    return best


def _bad_count(NB, N, D, W):
    """Ordered pairs (u, v) with dist(u, v) > D. NB is an (N, d) neighbour array."""
    idx = np.arange(N)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for j in range(NB.shape[1]):
            new |= reach[NB[:, j]]
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum(dtype=np.int64))
    return N * N - total


def _apply_switch(NB, n, rng):
    """Random 2-switch (a,b),(c,e) -> (a,e),(c,b) on absolute indices. Returns undo info or None."""
    d = NB.shape[1]
    a = rng.randrange(n)
    c = rng.randrange(n)
    if a == c:
        return None
    s = rng.randrange(d)
    t = rng.randrange(d)
    b = int(NB[a, s])
    e = int(NB[c, t])
    if (NB[a] == e).any() or (NB[c] == b).any():
        return None
    k = int(np.argmax(NB[b] == a))
    k2 = int(np.argmax(NB[e] == c))
    NB[a, s] = e
    NB[c, t] = b
    NB[b, k] = c
    NB[e, k2] = a
    return (a, s, b, c, t, e, k, k2)


def _undo(NB, mv):
    a, s, b, c, t, e, k, k2 = mv
    NB[a, s] = b
    NB[c, t] = e
    NB[b, k] = a
    NB[e, k2] = c


def _anneal(NB, n, D, deadline, rng, max_iter):
    """Anneal switches in place until the graph has diameter <= D. Returns True on success."""
    N = 2 * n
    W = (N + 63) // 64
    cur = _bad_count(NB, N, D, W)
    T = 1.5
    it = 0
    while cur > 0 and it < max_iter and time.monotonic() < deadline:
        it += 1
        T = max(0.15, T * 0.995)
        mv = _apply_switch(NB, n, rng)
        if mv is None:
            continue
        new = _bad_count(NB, N, D, W)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _undo(NB, mv)
    return cur == 0


def _splice(NB, n, d, rng):
    """Add one left vertex x = n and one right vertex y = 2n+1 of degree d each.

    Chooses d edges (a_i, b_i) with distinct a_i and distinct b_i, replaces them by
    (x, b_i) and (a_i, y). Old degrees are unchanged. Returns (n+1, NB2) or None.
    """
    order = list(range(n))
    rng.shuffle(order)
    usedA, usedB, chosen = set(), set(), []
    for a in order:
        if len(chosen) == d:
            break
        s = rng.randrange(d)
        b = int(NB[a, s])
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append((a, s, b))
    if len(chosen) < d:
        return None
    x, y = n, 2 * n + 1
    NB2 = np.zeros((2 * n + 2, d), dtype=np.int64)
    old = NB[:n]
    NB2[:n] = np.where(old >= n, old + 1, old)      # old lefts, rights shifted by one
    NB2[n + 1:2 * n + 1] = NB[n:2 * n]              # old rights, neighbours are lefts
    for i, (a, s, b) in enumerate(chosen):
        sb = int(np.argmax(NB[b] == a))
        NB2[a, s] = y
        NB2[b + 1, sb] = x
        NB2[x, i] = b + 1
        NB2[y, i] = a
    return n + 1, NB2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    best = _baseline(d, D)
    if d <= 2 or D == 2:
        return best

    moore = lib.moore_bound(d, D)

    # Growth from K_{d,d}.
    cur_n = d
    cur = np.zeros((2 * d, d), dtype=np.int64)
    cur[:d] = d + np.arange(d)[None, :]
    cur[d:] = np.arange(d)[None, :]

    fails = 0
    while time.monotonic() < deadline and 2 * (cur_n + 1) <= moore:
        spl = _splice(cur, cur_n, d, rng)
        if spl is None:
            break
        cand_n, cand_NB = spl
        budget = min(deadline, time.monotonic() + 3.0)
        if _anneal(cand_NB, cand_n, D, budget, rng, 4000):
            cur_n, cur = cand_n, cand_NB
            fails = 0
        else:
            fails += 1
            if fails >= 10:
                break

    total_n = 2 * cur_n
    if total_n > best[0]:
        edges = [(a, int(cur[a, s])) for a in range(cur_n) for s in range(d)]
        if lib.is_valid(total_n, edges, d, D):
            best = (total_n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
