import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: projective planes and generalized quadrangles.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side).
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 1500
STALL_LIMIT = 300
WALK_P = 0.03
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
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k."""
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
    """Count vertex pairs not within distance D, from A_0 and B_0 (bi-Cayley graph)."""
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
    """Hill-climb a connection set S to zero unreached pairs."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
    best_v = cur
    stall = 0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < WALK_P:
            S, cur = S2, v
        if v < best_v:
            best_v = v
            stall = 0
        else:
            stall += 1
        if stall > STALL_LIMIT:
            S, cur = fresh()
            best_v = cur
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid bi-Cayley lift."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# New construction: annealed search over d-regular bipartite graphs on N+N
# vertices, using edge-swap moves (which keep degrees and bipartiteness) and
# minimising the number of vertex pairs at distance greater than D.
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Unordered pairs at distance > D (unreachable pairs count), via bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _random_regular_bip(N, d, rng):
    """Union of d random perfect matchings between two copies of range(N), without repeats."""
    eset = set()
    for _ in range(d):
        ok = False
        for _attempt in range(100):
            p = list(range(N))
            rng.shuffle(p)
            if all((i, p[i]) not in eset for i in range(N)):
                ok = True
                break
        if not ok:
            return None
        for i in range(N):
            eset.add((i, p[i]))
    return list(eset)


def _anneal_regular(N, d, D, rng, deadline):
    """Simulated annealing over d-regular bipartite graphs on N+N vertices; (n, edges) or None."""
    E = _random_regular_bip(N, d, rng)
    if E is None:
        return None
    n = 2 * N
    eset = set(E)
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    cost = _bad_pairs(n, adj, D)
    m = len(E)
    t0 = time.monotonic()
    total = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.05

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** ((now - t0) / total)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        # Apply swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
        adj[a1].remove(N + b1)
        adj[N + b1].remove(a1)
        adj[a2].remove(N + b2)
        adj[N + b2].remove(a2)
        adj[a1].append(N + b2)
        adj[N + b2].append(a1)
        adj[a2].append(N + b1)
        adj[N + b1].append(a2)
        c2 = _bad_pairs(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            E[i] = (a1, b2)
            E[j] = (a2, b1)
        else:
            # Revert.
            adj[a1].remove(N + b2)
            adj[N + b2].remove(a1)
            adj[a2].remove(N + b1)
            adj[N + b1].remove(a2)
            adj[a1].append(N + b1)
            adj[N + b1].append(a1)
            adj[a2].append(N + b2)
            adj[N + b2].append(a2)

    if cost == 0:
        return n, [(a, N + b) for a, b in E]
    return None


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
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: aim just above the current best order.
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break

        if d == 5 and D == 5 and rng.random() < 0.7:
            # New construction: annealed regular bipartite search at order 2*lo.
            now = time.monotonic()
            remaining = deadline - now
            sub = now + max(0.5, 0.5 * remaining)
            res = _anneal_regular(lo, d, D, rng, min(sub, deadline))
            if res is not None:
                consider(res[0], res[1])
        else:
            # Bi-Cayley lift on a group of order N; the lift has 2N vertices.
            N = lo + rng.randrange(8)
            res = _search_bicayley(d, D, N, rng, deadline)
            if res is not None:
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
