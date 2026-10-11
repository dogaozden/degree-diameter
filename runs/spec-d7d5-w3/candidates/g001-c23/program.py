import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW family: direct simulated annealing on simple d-regular bipartite graphs.
#
# Instead of voltage lifts (a symmetric, structured family that stalls near the
# record), this searches the full space of simple d-regular bipartite graphs on
# 2N vertices. The state is an adjacency array adj[v, :] over all vertices
# (A side = 0..N-1, B side = N..2N-1). Moves are degree-preserving 2-switches.
# The cost is the number of ordered vertex pairs at distance > D, computed by
# bit-packed reachability (uint64 words, one bit per vertex), which is far
# cheaper than the dense boolean matrix used before.
#
# Every returned graph is re-checked with lib.is_valid before use. Any failure
# falls back to the best safe graph found so far.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)
_PATIENCE = 400


def _haar_adj(N, d, rng):
    """Random cyclic Haar start: A vertex a joins B vertex (a + s) mod N for d distinct shifts s."""
    S = rng.sample(range(N), d)
    adj = np.empty((2 * N, d), dtype=np.int64)
    for a in range(N):
        adj[a] = [N + (a + s) % N for s in S]
    for j in range(N):
        adj[N + j] = [(j - s) % N for s in S]
    return adj


def _bad(adj, D):
    """Ordered pairs (u, v) with distance > D (unreachable counted); 0 iff diameter <= D."""
    n2 = adj.shape[0]
    W = (n2 + 63) // 64
    reach = np.zeros((n2, W), dtype=np.uint64)
    idx = np.arange(n2)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[adj], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    pc = int(_POP8[reach.view(np.uint8)].sum())
    return n2 * n2 - pc


def _switch(adj, N, d, rng):
    """Random simple 2-switch on the A/B bipartition; returns a new adjacency array or None."""
    a1 = rng.randrange(N)
    a2 = rng.randrange(N)
    if a1 == a2:
        return None
    j1 = rng.randrange(d)
    j2 = rng.randrange(d)
    b1 = int(adj[a1, j1])
    b2 = int(adj[a2, j2])
    if b1 == b2 or (adj[a1] == b2).any() or (adj[a2] == b1).any():
        return None
    cand = adj.copy()
    cand[a1, j1] = b2
    cand[a2, j2] = b1
    r = cand[b1]
    r[int(np.argmax(r == a1))] = a2
    r = cand[b2]
    r[int(np.argmax(r == a2))] = a1
    return cand


def _anneal(N, d, D, rng, deadline):
    """Anneal a simple d-regular bipartite graph on 2N vertices to diameter <= D. Returns adj or None."""
    adj = _haar_adj(N, d, rng)
    cost = _bad(adj, D)
    it = 0
    last = 0
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        it += 1
        frac = (now - t0) / span
        T = 4.0 * (1.0 - frac) + 0.3
        cand = _switch(adj, N, d, rng)
        if cand is None:
            continue
        c = _bad(cand, D)
        delta = c - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            adj, cost = cand, c
            last = it
        elif it - last > _PATIENCE:
            # Stagnation: restart from a fresh structured start.
            adj = _haar_adj(N, d, rng)
            cost = _bad(adj, D)
            last = it
    return adj if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(2.0, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold new search: annealing over general simple bipartite graphs, with an
    # adaptive size ladder. Success grows the target, failure shrinks it slightly.
    if d >= 3 and D >= 3:
        N = max(d, best_n // 2 + 1)
        try:
            while time.monotonic() < end - 0.5:
                now = time.monotonic()
                remaining = end - now
                attempt_deadline = min(end, now + max(1.5, 0.25 * remaining))
                adj = _anneal(N, d, D, rng, attempt_deadline)
                if adj is not None:
                    edges = [(a, int(b)) for a in range(N) for b in adj[a]]
                    consider(2 * N, edges)
                    N += max(1, N // 30)
                else:
                    N = max(d, N - max(1, N // 100))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
