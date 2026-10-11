import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Structured baselines for D = 3 and D = 4 (projective planes, generalized quadrangles).
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
# Bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side), hill-climbed.
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 1500
STALL_LIMIT = 300
N_WINDOW = 8
SLICE = 10.0        # seconds per search slice
SA_CAP = 800        # largest total vertex count the dense annealer will touch
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
    """Count vertex pairs not within distance D, from A_0 and B_0 of the bi-Cayley graph."""
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
    """Hill-climb a connection set S (identity fixed) to zero unreached pairs."""
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
        v = _unreached(N, T, invs, S2, D)
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


def _bicayley_graph(d, D, N, rng, deadline):
    """Return (n, edges) of a valid bi-Cayley lift on 2N vertices, or None."""
    res = _search_bicayley(d, D, N, rng, deadline)
    if res is None:
        return None
    T, S = res
    return 2 * N, [(x, N + T[x][g]) for x in range(N) for g in S]


# ----------------------------------------------------------------------------
# Bold change: simulated annealing over general d-regular bipartite graphs.
# State: a dense 0/1 biadjacency structure kept as a float32 adjacency matrix F
# (with self-loops, so R @ F expands balls). Moves are double edge swaps, which
# keep the graph simple and d-regular. Cost = ordered pairs at distance > D.
# ----------------------------------------------------------------------------

def _ball_cost(F, D):
    """Number of ordered vertex pairs at distance greater than D."""
    n = F.shape[0]
    R = np.eye(n, dtype=np.float32)
    for _ in range(D):
        R = (R @ F > 0).astype(np.float32)
    return int(n * n - R.sum())


def _flip(F, s, a, b, val):
    """Set the symmetric entries joining left vertex a and right vertex b."""
    F[a, s + b] = val
    F[s + b, a] = val


def _sa_regular(d, D, s, rng, deadline):
    """Anneal a d-regular bipartite graph with s vertices per side; return (n, edges) or None."""
    n = 2 * s
    F = np.zeros((n, n), dtype=np.float32)
    np.fill_diagonal(F, 1.0)
    shifts = rng.sample(range(s), d)
    ea, eb = [], []
    for a in range(s):
        for sh in shifts:
            b = (a + sh) % s
            ea.append(a)
            eb.append(b)
            _flip(F, s, a, b, 1.0)
    E = len(ea)

    cost = _ball_cost(F, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0, T1 = 2.0, 0.25

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        i = rng.randrange(E)
        j = rng.randrange(E)
        a1, b1 = ea[i], eb[i]
        a2, b2 = ea[j], eb[j]
        if a1 == a2 or b1 == b2 or F[a1, s + b2] or F[a2, s + b1]:
            continue
        _flip(F, s, a1, b1, 0.0)
        _flip(F, s, a2, b2, 0.0)
        _flip(F, s, a1, b2, 1.0)
        _flip(F, s, a2, b1, 1.0)
        c2 = _ball_cost(F, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            eb[i] = b2
            eb[j] = b1
        else:
            _flip(F, s, a1, b2, 0.0)
            _flip(F, s, a2, b1, 0.0)
            _flip(F, s, a1, b1, 1.0)
            _flip(F, s, a2, b2, 1.0)

    if cost != 0:
        return None
    rows, cols = np.nonzero(F[:s, s:])
    edges = [(int(a), int(s + b)) for a, b in zip(rows, cols)]
    return n, edges


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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: alternate annealing (new construction family) with bi-Cayley
    # climbs, always aiming one step above the current best order.
    while best[0] < moore:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        slice_end = min(deadline, now + SLICE)

        if rng.random() < 0.5 and 2 * lo <= SA_CAP and lo >= d:
            res = _sa_regular(d, D, lo, rng, slice_end)
            if res is not None:
                consider(res[0], res[1])
        else:
            N = lo + rng.randrange(N_WINDOW)
            if N > moore // 2:
                N = lo
            res = _bicayley_graph(d, D, N, rng, slice_end)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
