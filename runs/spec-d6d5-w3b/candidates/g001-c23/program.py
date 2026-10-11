import math
import random
import time

import lib


def _cost(k, N, mt, darts, D):
    """Number of (start, vertex) pairs not reached within D steps, from one identity vertex per fibre.

    The lift is invariant under left multiplication by the group, so checking BFS balls around the
    identity of each of the 2k fibres is enough to certify diameter <= D. Zero means valid.
    """
    n = 2 * k * N
    adj = [[] for _ in range(n)]
    for i, j, g in darts:
        ab = i * N
        bb = (k + j) * N
        for x in range(N):
            a = ab + x
            b = bb + mt[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for f in range(2 * k):
        s = f * N
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _edges(k, N, mt, darts):
    """Materialise the lift: A-fibre i (vertices i*N+x) joined to B-fibre j (vertices (k+j)*N+x*g)."""
    n = 2 * k * N
    es = set()
    for i, j, g in darts:
        for x in range(N):
            a = i * N + x
            b = (k + j) * N + mt[x][g]
            es.add((a, b))
    return n, sorted(es)


def _table(m, kk, r, cache):
    """Multiplication table of Z_m x|_r Z_kk, cached by parameters."""
    key = (m, kk, r)
    if key in cache:
        return cache[key]
    if len(cache) > 40:
        cache.clear()
    N, mul, _ = lib.semidirect_group(m, kk, r)
    mt = [[mul(x, y) for y in range(N)] for x in range(N)]
    cache[key] = (N, mt)
    return cache[key]


def _anneal(k, N, mt, d, D, rng, deadline, patience):
    """Random search over a d-regular k x k multiplicity pattern and group voltages.

    Accepts sideways moves; stops after `patience` steps without strict improvement.
    Returns the dart list (i, j, g) with cost 0, or None.
    """
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            M[i][perm[i]] += 1
    darts = []
    for i in range(k):
        for j in range(k):
            if M[i][j] > N:
                return None
            for g in rng.sample(range(N), M[i][j]):
                darts.append([i, j, g])
    cur = _cost(k, N, mt, darts, D)
    stall = 0
    while cur > 0 and stall < patience and time.monotonic() < deadline:
        t = rng.randrange(len(darts))
        i, j, g_old = darts[t]
        taken = {dg[2] for dg in darts if dg[0] == i and dg[1] == j}
        cand = rng.randrange(N)
        if cand in taken:
            stall += 1
            continue
        darts[t][2] = cand
        new = _cost(k, N, mt, darts, D)
        if new <= cur:
            stall = 0 if new < cur else stall + 1
            cur = new
        else:
            darts[t][2] = g_old
            stall += 1
    return darts if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 4.0))

    if d < 1 or D < 1:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    best = (2, [(0, 1)])
    if d >= 2 and D >= 2:
        cand = lib.haar_graph(d, range(d))  # K_{d,d}
        if lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    best_n = best[0]

    rng = random.Random(seed)
    cache = {}
    while time.monotonic() < deadline:
        k = rng.choice((2, 2, 3, 3, 1, 4))
        base_per = best_n // (2 * k)
        N = base_per + 1 + rng.randrange(0, 1 + base_per // 200)
        opts = [kk for kk in (1, 2, 3, 4, 6) if N % kk == 0]
        kk = rng.choice(opts)
        m = N // kk
        if kk == 1:
            r = 1
        else:
            rs = [x for x in range(1, m)
                  if math.gcd(x, m) == 1 and pow(x, kk, m) == 1 % m]
            if not rs:
                continue
            r = rng.choice(rs)
        NN, mt = _table(m, kk, r, cache)
        darts = _anneal(k, NN, mt, d, D, rng, deadline, patience=500)
        if darts is None:
            continue
        n, edges = _edges(k, NN, mt, darts)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
    return best
