import math
import random
import time

import lib


def _mul_table(N, mul):
    return [[mul(x, y) for y in range(N)] for x in range(N)]


def _groups(N, rng):
    """Semidirect products Z_m x| Z_ks of order N (cyclic when r = 1), shuffled and capped."""
    out = []
    for ks in range(1, N + 1):
        if N % ks:
            continue
        m = N // ks
        if m == 1:
            out.append((1, ks, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, ks, m) == 1:
                out.append((m, ks, r))
    rng.shuffle(out)
    return out[:12]


def _adjacency(k, N, mt, darts):
    """Adjacency of the lift. A-block i is vertices i*N..i*N+N-1; B-block j is (k+j)*N..; dart (i, j, g)
    joins A(i, x) to B(j, x*g)."""
    n = 2 * k * N
    adj = [[] for _ in range(n)]
    for i, j, g in darts:
        ba = i * N
        bb = (k + j) * N
        for x in range(N):
            a = ba + x
            b = bb + mt[x][g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _cost(k, N, mt, darts, D):
    """Number of (block representative, vertex) pairs at distance > D.

    The lift admits left multiplication by the group, which is transitive on each block, so
    eccentricities are constant on blocks and checking one representative per block is exact.
    Zero cost means the lift has diameter <= D and is connected.
    """
    adj = _adjacency(k, N, mt, darts)
    n = 2 * k * N
    bad = 0
    for b in range(2 * k):
        s = b * N
        seen = [False] * n
        seen[s] = True
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        bad += n - cnt
    return bad


def _edges(k, N, mt, darts):
    es = set()
    for i, j, g in darts:
        for x in range(N):
            a = i * N + x
            b = (k + j) * N + mt[x][g]
            es.add((a, b) if a < b else (b, a))
    return sorted(es)


def _search(k, d, D, N, mt, rng, slice_end):
    """Simulated-style hill climb over dart voltages of a k+k base multigraph lifted over a group of order N.

    Each base vertex gets d darts (one per random permutation), so every lifted vertex has degree <= d.
    Returns the dart list once the lift has diameter <= D, or None when the time slice runs out.
    """
    while time.monotonic() < slice_end:
        perms = []
        for _ in range(d):
            p = list(range(k))
            rng.shuffle(p)
            perms.append(p)
        darts = [[i, perms[a][i], rng.randrange(N)] for a in range(d) for i in range(k)]
        cur = _cost(k, N, mt, darts, D)
        stale = 0
        while cur > 0 and stale < 1500:
            if time.monotonic() >= slice_end:
                return None
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(N)
            new = _cost(k, N, mt, darts, D)
            if new <= cur:
                stale = stale + 1 if new == cur else 0
                cur = new
            else:
                darts[idx][2] = old
                stale += 1
        if cur == 0:
            return darts
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d <= 0 or D <= 0:
        return 1, []

    # Special case: projective plane incidence meets the Moore bound when d-1 is a prime power, D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Safe fallback: a single edge (valid for any d >= 1, D >= 1); upgrade to K_{d,d} when D >= 2.
    best = (2, [(0, 1)])
    if D >= 2 and d >= 2:
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            best = (n, e)
    best_n = best[0]

    mb = lib._moore_bound(d, D)
    budget = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = start + budget
    slice_len = max(1.5, budget / 8.0)
    rng = random.Random(seed)

    # Bold search: bipartite lifts over non-cyclic groups with small base graphs (k + k vertices).
    base_sizes = (1, 2, 3, 4)
    while time.monotonic() < deadline and best_n < mb:
        for k in base_sizes:
            if time.monotonic() >= deadline or best_n >= mb:
                break
            # Smallest group order that could beat the current best with this base size.
            N = -(-(best_n + 1) // (2 * k))
            if N < 1 or 2 * k * N > mb or N > 300:
                continue
            groups = _groups(N, rng)
            if not groups:
                continue
            m, ks, r = rng.choice(groups)
            try:
                order, mul, _ = lib.semidirect_group(m, ks, r)
            except ValueError:
                continue
            if order != N:
                continue
            mt = _mul_table(order, mul)
            slice_end = min(deadline, time.monotonic() + slice_len)
            darts = _search(k, d, D, order, mt, rng, slice_end)
            if darts is None:
                continue
            n = 2 * k * order
            edges = _edges(k, order, mt, darts)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n

    return best
