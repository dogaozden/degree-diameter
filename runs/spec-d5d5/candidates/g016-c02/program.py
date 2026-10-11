import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_SEED = 12   # groups tried for one order N
ITERS = 1000               # annealing steps per (group, connection set) try


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley seeds over semidirect products Z_m x| Z_k of order N.
# Vertices A_x, B_y (x, y in G); A_x ~ B_{x s} for s in S, |S| = d.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached_S(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
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


def _anneal_S(N, T, invs, d, D, rng, iters, deadline):
    """Anneal S = {0, s_1, ..., s_{d-1}}; return (best_S, best_cost). Cost 0 means exact."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached_S(N, T, invs, S, D)
    best_S, best_c = S[:], cur
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached_S(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
            if cur < best_c:
                best_S, best_c = S[:], cur
    return best_S, best_c


def _seed(N, d, D, rng, deadline):
    """Best bi-Cayley seed (T, S, cost) of order N found before deadline, or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    best = None
    for m, k, r in groups[:MAX_GROUPS_PER_SEED]:
        if time.monotonic() > deadline:
            break
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S, c = _anneal_S(N, T, invs, d, D, rng, ITERS, deadline)
        if best is None or c < best[2]:
            best = (T, S, c)
        if c == 0:
            break
    return best


def _adj_from(N, T, S):
    """Adjacency lists over 2N vertices (A = 0..N-1, B = N..2N-1) of the bi-Cayley graph."""
    adj = [[] for _ in range(2 * N)]
    for x in range(N):
        for g in S:
            y = T[x][g]
            adj[x].append(N + y)
            adj[N + y].append(x)
    return adj


# ----------------------------------------------------------------------------
# Unstructured repair: double-edge swaps on a bipartite d-regular graph,
# annealing the number of ordered pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad(adj, n, D):
    """Total number of (vertex, vertex) pairs not within distance D (bitset balls)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _repair(N, adj, d, D, rng, deadline):
    """Anneal double-edge swaps until diameter <= D; return adj on success, else None."""
    n = 2 * N
    cur = _bad(adj, n, D)
    if cur == 0:
        return adj
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        temp = max(0.3, 3.0 * (1.0 - frac))
        a1 = rng.randrange(N)
        i = rng.randrange(d)
        b1 = adj[a1][i]
        a2 = rng.randrange(N)
        k = rng.randrange(d)
        b2 = adj[a2][k]
        if a1 == a2 or b1 == b2:
            continue
        if b2 in adj[a1] or b1 in adj[a2]:
            continue
        ja = adj[b2].index(a2)
        jb = adj[b1].index(a1)
        adj[a1][i] = b2
        adj[a2][k] = b1
        adj[b2][ja] = a1
        adj[b1][jb] = a2
        new = _bad(adj, n, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = new
            if cur == 0:
                return adj
        else:
            adj[a1][i] = b1
            adj[a2][k] = b2
            adj[b2][ja] = a2
            adj[b1][jb] = a1
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, time_limit - 5.0)
    deadline = start + max(1.0, budget)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Safe fallbacks.
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices

    # Ladder: at each order N try an exact bi-Cayley seed; if none is exact,
    # start from the least-bad seed and repair it with edge swaps.
    N = max(d + 1, best_n // 2 + 1)
    while N <= Nmax and time.monotonic() < deadline:
        now = time.monotonic()
        seed_end = now + 0.5 * (deadline - now)
        res = _seed(N, d, D, rng, seed_end)
        if res is None:
            break
        T, S, c = res
        adj = _adj_from(N, T, S)
        if c > 0:
            adj = _repair(N, adj, d, D, rng, deadline)
            if adj is None:
                break
        edges = [(a, b) for a in range(N) for b in adj[a]]
        consider(2 * N, edges)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
