import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Candidate generators.
#   1. K_{d,d} (always valid for D >= 2) as the safe fallback.
#   2. PG(2, q) incidence graph for D = 3.
#   3. Cyclic bi-Cayley (Haar-type) lifts found by hill-climbing over
#      connection sets, with an upward sweep in order.
#   4. NEW: simulated annealing over bipartite graphs with exact degree
#      preservation (2-switch moves). The cost is the number of vertex pairs
#      at distance > D, computed with boolean matrix powers of (I + A).
#      It does not assume any symmetry of the target graph.
# Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------


def _cyclic_unreached(N, S, D):
    """Pairs not within distance D, counted from A_0 and B_0 (bi-Cayley: A_x ~ B_{x+s})."""
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    for s in S:
                        v = N + (u + s) % N
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    x = u - N
                    for s in S:
                        v = (x - s) % N
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - cnt
    return total


def _cyclic_climb(N, d, D, rng, iters, deadline):
    """Hill-climb a d-subset S of Z_N to zero unreached pairs (sideways moves allowed)."""
    S = rng.sample(range(N), d)
    cur = _cyclic_unreached(N, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _cyclic_unreached(N, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


def _cyclic_sweep(d, D, lo_n, moore, rng, deadline):
    """Sweep bi-Cayley orders upward from lo_n; return the largest (n, edges) found."""
    N = max(lo_n, d)
    fails = 0
    found = None
    while N <= moore // 2 and time.monotonic() < deadline and fails < 25:
        S = None
        for _ in range(2):
            S = _cyclic_climb(N, d, D, rng, 150, deadline)
            if S is not None:
                break
        if S is not None:
            fails = 0
            edges = [(x, N + (x + s) % N) for x in range(N) for s in S]
            found = (2 * N, edges)
        else:
            fails += 1
        N += 1
    return found


# ----------------------------------------------------------------------------
# Annealing over bipartite graphs with N vertices per side, max degree d.
# ----------------------------------------------------------------------------

def _bad(N, edges, D):
    """Unordered pairs at distance > D in the bipartite graph on 2N vertices (edges are (a, b), 0 <= a,b < N)."""
    M = np.zeros((2 * N, 2 * N), dtype=np.float32)
    if edges:
        a = np.fromiter((e[0] for e in edges), dtype=np.int64, count=len(edges))
        b = np.fromiter((e[1] + N for e in edges), dtype=np.int64, count=len(edges))
        M[a, b] = 1.0
        M[b, a] = 1.0
    np.fill_diagonal(M, 1.0)
    P = M
    for _ in range(D - 1):
        P = ((P @ M) > 0).astype(np.float32)
    nnz = int(np.count_nonzero(P))
    return (4 * N * N - nnz) // 2


def _anneal(N, d, D, rng, deadline):
    """Anneal a bipartite graph on N+N vertices, degree <= d, to diameter <= D. Returns edge list or None."""
    if N < d:
        return None
    adjA = [set() for _ in range(N)]
    adjB = [set() for _ in range(N)]
    for _ in range(d):
        p = list(range(N))
        rng.shuffle(p)
        for i in range(N):
            j = p[i]
            if len(adjA[i]) < d and len(adjB[j]) < d and j not in adjA[i]:
                adjA[i].add(j)
                adjB[j].add(i)
    defA = [i for i in range(N) if len(adjA[i]) < d]
    defB = [j for j in range(N) if len(adjB[j]) < d]
    pairs = [(i, j) for i in defA for j in defB if j not in adjA[i]]
    rng.shuffle(pairs)
    for i, j in pairs:
        if len(adjA[i]) < d and len(adjB[j]) < d and j not in adjA[i]:
            adjA[i].add(j)
            adjB[j].add(i)

    edges = [(i, j) for i in range(N) for j in adjA[i]]
    if not edges:
        return None
    eset = set(edges)
    E = len(edges)
    cost = _bad(N, edges, D)
    if cost == 0:
        return [(a, N + b) for a, b in edges]

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 1.0
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = min(1.0, (now - t0) / span)
            T = 1.5 * (0.03 / 1.5) ** frac
        k1 = rng.randrange(E)
        k2 = rng.randrange(E)
        if k1 == k2:
            continue
        a1, b1 = edges[k1]
        a2, b2 = edges[k2]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in eset or n2 in eset:
            continue
        # Apply the 2-switch (keeps every degree unchanged).
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add(n1)
        eset.add(n2)
        edges[k1] = n1
        edges[k2] = n2
        c2 = _bad(N, edges, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            eset.discard(n1)
            eset.discard(n2)
            eset.add((a1, b1))
            eset.add((a2, b2))
            edges[k1] = (a1, b1)
            edges[k2] = (a2, b2)

    if cost == 0:
        return [(a, N + b) for a, b in edges]
    return None


def _anneal_driver(d, D, lo_n, moore, rng, deadline):
    """Try increasing per-side sizes with annealing; return the largest (n, edges) found."""
    best = None
    N = max(lo_n, d)
    step = max(2, N // 10)
    last_ok = None
    fails = 0
    while time.monotonic() < deadline and N <= moore // 2 and fails < 6:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, 0.4 * (deadline - now)))
        E = _anneal(N, d, D, rng, slice_end)
        if E is not None:
            best = (2 * N, E)
            last_ok = N
            N += step
        else:
            fails += 1
            if last_ok is not None:
                step = max(1, step // 2)
                N = last_ok + step
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and max degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3: projective plane incidence graph (meets the Moore bound when d - 1 is a prime power).
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break
        if best[0] >= moore:
            return best

    # Cyclic bi-Cayley sweep, using a share of the budget.
    cyc_deadline = start + 0.3 * budget
    cand = _cyclic_sweep(d, D, best[0] // 2 + 1, moore, rng, cyc_deadline)
    if cand is not None:
        consider(*cand)
    if best[0] >= moore:
        return best

    # New construction: annealing over degree-preserving 2-switch moves.
    cand = _anneal_driver(d, D, best[0] // 2 + 1, moore, rng, deadline)
    if cand is not None:
        consider(*cand)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
