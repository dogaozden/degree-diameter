import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------

MAX_GROUPS = 12        # groups tried per order N in one bi-Cayley attempt
CLIMB_ITERS = 1500     # hill-climb steps per restart (exact search)
STALL_LIMIT = 300      # re-randomize after this many non-improving steps
SOFT_ITERS = 600       # soft-climb steps for the base of the completion method
COMPLETE_K = 16        # candidate edges evaluated per greedy completion step
NEW_PROB = 0.6         # fraction of attempts using the completion method
N_WINDOW = 8           # bi-Cayley orders tried in a window just above the record
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Baseline constructions (D = 3 and D = 4 families).
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side).
# Vertices A_x (index x) and B_y (index N + y); A_x ~ B_{x g} for g in S.
# Left translation is an automorphism preserving each side, so eccentricities
# from A_0 and B_0 decide the diameter. Identity is WLOG in S.
# ----------------------------------------------------------------------------

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
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k; T[x][g] = x*g, invs[g] = g^-1."""
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


def _unreached(N, T, invs, S, D, cap=None):
    """Count (source, vertex) pairs not within distance D, sources A_0 and B_0.

    If cap is given, may return early with a value > cap once the total exceeds cap.
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
        if cap is not None and total > cap:
            return total
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb S to zero unreached pairs; sideways moves allowed; restarts on stall."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
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
        v = _unreached(N, T, invs, S2, D, cap=cur)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Exact search: try several groups of order N; return (T, S) for the first valid lift."""
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
# NEW: soft base + greedy bad-pair completion.
#
# A (d-1)-regular bi-Cayley base on 2N vertices is climbed to a low (not
# necessarily zero) number of unreached pairs. Every vertex then has one spare
# slot. The completion repeatedly takes a bad pair (u, v) whose endpoints both
# have spare degree and lie on opposite sides, scores a few such candidates by
# the exact number of bad pairs after adding the edge, and commits the best.
# Adding an edge never increases distances, so the bad count is monotone and
# the process only ends by reaching zero or running out of spare pairs.
# ----------------------------------------------------------------------------

def _soft_climb(N, T, invs, k, D, rng, iters, deadline):
    """Climb S (size k, identity included) to reduce unreached pairs; return (S, cost)."""
    S = [0] + rng.sample(range(1, N), k - 1)
    cur = _unreached(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, k)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D, cap=cur)
        if v <= cur:
            S, cur = S2, v
    return S, cur


def _reach_masks(n, adj, D):
    """Per-vertex bitmask of the ball of radius D (bit w set iff distance <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _bad(n, reach):
    """Number of unordered vertex pairs at distance greater than D."""
    return sum(n - r.bit_count() for r in reach) // 2


def _complete(n, base, d, D, rng, deadline, K=COMPLETE_K):
    """Greedily add edges between opposite sides (degree <= d) to remove bad pairs.

    Returns the edge list of a graph with zero bad pairs, or None.
    """
    half = n // 2
    side = [0] * half + [1] * half
    adj = [set() for _ in range(n)]
    for u, v in base:
        adj[u].add(v)
        adj[v].add(u)
    full = (1 << n) - 1
    reach = _reach_masks(n, adj, D)
    cur = _bad(n, reach)

    while cur > 0:
        if time.monotonic() > deadline:
            return None
        cands = []
        for u in range(n):
            if len(adj[u]) >= d:
                continue
            miss = full ^ reach[u]
            while miss:
                low = miss & -miss
                v = low.bit_length() - 1
                miss ^= low
                if v > u and len(adj[v]) < d and side[u] != side[v]:
                    cands.append((u, v))
        if not cands:
            return None
        rng.shuffle(cands)
        best = None
        for u, v in cands[:K]:
            if time.monotonic() > deadline:
                break
            adj[u].add(v)
            adj[v].add(u)
            c = _bad(n, _reach_masks(n, adj, D))
            adj[u].discard(v)
            adj[v].discard(u)
            if best is None or c < best[0]:
                best = (c, u, v)
                if c == 0:
                    break
        if best is None:
            return None
        c, u, v = best
        adj[u].add(v)
        adj[v].add(u)
        reach = _reach_masks(n, adj, D)
        cur = _bad(n, reach)

    return sorted({(min(u, v), max(u, v)) for u in range(n) for v in adj[u]})


def _soft_attempt(d, D, N, rng, deadline):
    """Soft-climb a (d-1)-regular bi-Cayley base of order N, then complete it to degree d."""
    if d - 1 < 2 or N - 1 < d - 1:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        S, _cost = _soft_climb(N, T, invs, d - 1, D, rng, SOFT_ITERS, deadline)
        base = [(x, N + T[x][g]) for x in range(N) for g in S]
        E = _complete(2 * N, base, d, D, rng, deadline)
        if E is not None:
            return 2 * N, E
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and meets the Moore bound 2d for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured baselines.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: beat the current best order.
    while best_n < moore and time.monotonic() < deadline:
        lo = best_n // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)
        if rng.random() < NEW_PROB:
            res = _soft_attempt(d, D, N, rng, deadline)
            if res is not None:
                consider(res[0], res[1])
        else:
            if N <= d:
                continue
            res = _search_bicayley(d, D, N, rng, deadline)
            if res is not None:
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
