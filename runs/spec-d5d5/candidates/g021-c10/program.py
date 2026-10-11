import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Phase 1: bi-Cayley lifts over Z_m x|_r Z_k with annealed connection sets.
# Gives a valid d-regular bipartite seed graph quickly.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8
CLIMB_ITERS = 800
_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (order, mul, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count ordered pairs (source, target) at distance > D from A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translation is an
    automorphism that is transitive on each side, so two sources suffice.
    """
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over a connection set S (identity fixed as one dart)."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


def _phase_bicayley(d, D, rng, deadline, moore, consider, cur_best):
    """Grow the best bi-Cayley lift found before the deadline."""
    while cur_best() < moore and time.monotonic() < deadline:
        lo = cur_best() // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(max(2, lo // 10))
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k2, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            _, _, T, invs = _tables(m, k2, r)
            S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])


# ----------------------------------------------------------------------------
# Phase 2: vertex insertion into a d-regular bipartite graph, followed by
# edge-switch annealing that drives the number of far-apart pairs to zero.
# Adjacency is stored as adjA (n x d, B-local indices) and adjB (n x d,
# A-local indices). Global numbering: A = 0..n-1, B = n..2n-1.
# ----------------------------------------------------------------------------

_POPCNT = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _to_adj(n_tot, edges, d):
    """Convert a bipartite d-regular edge list (A first, B second) to local adjacency arrays."""
    n = n_tot // 2
    adjA = [[] for _ in range(n)]
    adjB = [[] for _ in range(n)]
    for u, v in edges:
        if u > v:
            u, v = v, u
        if not (u < n <= v):
            return None
        adjA[u].append(v - n)
        adjB[v - n].append(u)
    if any(len(x) != d for x in adjA) or any(len(x) != d for x in adjB):
        return None
    return np.array(adjA, dtype=np.int64), np.array(adjB, dtype=np.int64), n


def _edges_of(adjA, n):
    return [(a, n + b) for a, row in enumerate(adjA.tolist()) for b in row]


def _pack_balls(N, nbr, D):
    """Bitset of vertices within distance D of each vertex (rows of uint64 words)."""
    W = (N + 63) // 64
    ball = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N)
    ball[idx, idx // 64] = np.uint64(1) << (idx % 64).astype(np.uint64)
    for _ in range(D):
        ball = ball | np.bitwise_or.reduce(ball[nbr], axis=1)
    return ball


def _cost(nbr, N, D):
    """Ordered pairs at distance > D. Zero iff the graph has diameter <= D."""
    ball = _pack_balls(N, nbr, D)
    reached = int(_POPCNT[ball.view(np.uint8)].sum())
    return N * N - reached


def _try_switch(adjA, adjB, n, d, rng):
    """Pick a valid 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1)."""
    a1 = rng.randrange(n)
    a2 = rng.randrange(n)
    if a1 == a2:
        return None
    j1 = rng.randrange(d)
    j2 = rng.randrange(d)
    b1 = int(adjA[a1, j1])
    b2 = int(adjA[a2, j2])
    if b1 == b2:
        return None
    if (adjA[a1] == b2).any() or (adjA[a2] == b1).any():
        return None
    k1 = int(np.nonzero(adjB[b1] == a1)[0][0])
    k2 = int(np.nonzero(adjB[b2] == a2)[0][0])
    return a1, j1, a2, j2, b1, b2, k1, k2


def _anneal_repair(adjA, adjB, n, d, D, rng, end):
    """Edge-switch annealing until diameter <= D (True) or the time limit (False)."""
    tot = 2 * n
    cost = _cost(np.vstack([adjA + n, adjB]), tot, D)
    if cost == 0:
        return True
    t_start = time.monotonic()
    span = max(1e-3, end - t_start)
    T0 = max(1.0, 0.02 * cost)
    while True:
        now = time.monotonic()
        if now >= end:
            break
        frac = (now - t_start) / span
        T = T0 * (1.0 - frac) + 0.05
        mv = _try_switch(adjA, adjB, n, d, rng)
        if mv is None:
            continue
        a1, j1, a2, j2, b1, b2, k1, k2 = mv
        adjA[a1, j1] = b2
        adjA[a2, j2] = b1
        adjB[b1, k1] = a2
        adjB[b2, k2] = a1
        c2 = _cost(np.vstack([adjA + n, adjB]), tot, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost == 0:
                return True
        else:
            adjA[a1, j1] = b1
            adjA[a2, j2] = b2
            adjB[b1, k1] = a1
            adjB[b2, k2] = a2
    return False


def _insert(adjA, adjB, n, d, rng):
    """Add one A-vertex and one B-vertex by rewiring a random matching of size d.

    Removes (a_i, b_i) for i = 1..d and adds (a*, b_i) and (a_i, b*). All degrees stay d.
    Returns new copies of the arrays, leaving the inputs untouched.
    """
    pairs = None
    for _ in range(30):
        order = list(range(n))
        rng.shuffle(order)
        used = set()
        chosen = []
        for a in order:
            j = rng.randrange(d)
            b = int(adjA[a, j])
            if b in used:
                continue
            used.add(b)
            chosen.append((a, j, b))
            if len(chosen) == d:
                break
        if len(chosen) == d:
            pairs = chosen
            break
    if pairs is None:
        return None
    A2 = np.zeros((n + 1, d), dtype=np.int64)
    A2[:n] = adjA
    B2 = np.zeros((n + 1, d), dtype=np.int64)
    B2[:n] = adjB
    for i, (a, j, b) in enumerate(pairs):
        k = int(np.nonzero(B2[b] == a)[0][0])
        A2[a, j] = n          # new B-vertex b* = n
        B2[b, k] = n          # new A-vertex a* = n
        A2[n, i] = b
        B2[n, i] = a
    return A2, B2, n + 1


def _phase_repair(d, D, adjA, adjB, n, rng, deadline, moore, consider):
    """Repeatedly insert a vertex pair and repair; keep each success."""
    while True:
        now = time.monotonic()
        if now >= deadline or 2 * (n + 1) > moore:
            break
        ins = _insert(adjA, adjB, n, d, rng)
        if ins is None:
            break
        A2, B2, n2 = ins
        stage_end = min(deadline, now + max(1.5, 0.12 * (deadline - now)))
        if _anneal_repair(A2, B2, n2, d, D, rng, stage_end):
            adjA, adjB, n = A2, B2, n2
            consider(2 * n, _edges_of(adjA, n))


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        N = 2 * D
        return N, [(i, (i + 1) % N) for i in range(N)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3: projective plane incidence graph when d - 1 is a prime power.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n3, e3 = lib.projective_plane_incidence(q)
                consider(n3, e3)
                break
        if best[0] >= moore:
            return best

    # Phase 1: bi-Cayley lifts, a short time slice for a good seed.
    p1 = start + 0.3 * budget
    _phase_bicayley(d, D, rng, p1, moore, consider, lambda: best[0])

    # Phase 2: insertion and switch-repair, starting from the best valid graph.
    if best[0] < moore:
        st = _to_adj(best[0], best[1], d)
        if st is not None:
            adjA, adjB, n = st
            _phase_repair(d, D, adjA, adjB, n, rng, deadline, moore, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
