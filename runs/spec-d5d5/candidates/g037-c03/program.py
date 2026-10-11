import math
import random
import time

import lib

MAX_GROUPS = 10      # groups tried per (k, N) before resampling
ANNEAL_ITERS = 1500  # annealing steps per attempt
SLICE = 4.0          # seconds per annealing attempt


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups(N):
    """Semidirect parameters (m, k, r) giving groups Z_m x|_r Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(N, m, k, r):
    """Multiplication table of the group with elements 0..N-1."""
    _, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(x, g) for g in range(N)] for x in range(N)]


def _cost(k, N, T, darts, D):
    """Number of (source, vertex) pairs at distance > D, over the 2k fibre identities.

    Lift: vertices A(i, x) = i*N + x and B(j, y) = k*N + j*N + y. Dart (i, j, g)
    joins A(i, x) to B(j, x*g). Left translation is an automorphism, so covering
    the identity of each fibre suffices for the diameter.
    """
    nv = 2 * k * N
    off = k * N
    adj = [[] for _ in range(nv)]
    for i, j, g in darts:
        ai, bj = i * N, off + j * N
        for x in range(N):
            a = ai + x
            b = bj + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    sources = [i * N for i in range(k)] + [off + j * N for j in range(k)]
    for src in sources:
        seen = bytearray(nv)
        seen[src] = 1
        frontier = [src]
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
        total += nv - cnt
    return total


def _anneal(k, N, T, d, D, rng, deadline):
    """Simulated annealing over darts (i, j, g); each A and B vertex gets exactly d darts."""
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append([i, perm[i], rng.randrange(N)])
    cur = _cost(k, N, T, darts, D)
    for it in range(ANNEAL_ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / ANNEAL_ITERS))
        new = [list(t) for t in darts]
        if k == 1 or rng.random() < 0.5:
            new[rng.randrange(len(new))][2] = rng.randrange(N)
        else:
            a, b = rng.sample(range(len(new)), 2)
            new[a][1], new[b][1] = new[b][1], new[a][1]
        v = _cost(k, N, T, new, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _lift_edges(k, N, T, darts):
    """Expand darts into the simple edge list of the lifted graph."""
    off = k * N
    es = set()
    for i, j, g in darts:
        for x in range(N):
            a = i * N + x
            b = off + j * N + T[x][g]
            es.add((a, b) if a < b else (b, a))
    return 2 * k * N, sorted(es)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        if lib.is_valid(best_n, best_e, d, D):
            return best_n, best_e
        return 1, []

    if D == 1:
        consider(2, [(0, 1)])
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    def search():
        nonlocal best_n, best_e
        moore = lib._moore_bound(d, D)
        while time.monotonic() < deadline:
            opts = []
            for k in (1, 1, 2, 2, 3, 4):
                nmin = best_n // (2 * k) + 1   # need 2*k*N > best_n
                nmax = moore // (2 * k)
                if nmin <= nmax:
                    opts.append((k, nmin, nmax))
            if not opts:
                return
            k, nmin, nmax = rng.choice(opts)
            N = rng.randint(nmin, min(nmax, nmin + 3))
            groups = _groups(N)
            rng.shuffle(groups)
            for m, kk, r in groups[:MAX_GROUPS]:
                now = time.monotonic()
                if now >= deadline:
                    return
                T = _table(N, m, kk, r)
                darts = _anneal(k, N, T, d, D, rng, min(deadline, now + SLICE))
                if darts is not None:
                    n, e = _lift_edges(k, N, T, darts)
                    if n > best_n and lib.is_valid(n, e, d, D):
                        best_n, best_e = n, e
                    break

    if d >= 2 and D >= 2 and time.monotonic() < deadline:
        search()

    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []
    return best_n, best_e
