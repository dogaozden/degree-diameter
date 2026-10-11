import math
import random
import time

import lib

ITER = 3000          # annealing steps per restart
MAX_P = 12           # maximum number of base vertices per side
MAX_CANDS = 60       # cap on (order, p, N) candidates
_TABLES = {}         # cache of group multiplication tables


# ----------------------------------------------------------------------------
# Safe baselines (always checked with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Generic bipartite voltage lifts over semidirect products Z_m x| Z_k.
#
# Base graph: p vertices A_0..A_{p-1} and p vertices B_0..B_{p-1}.
# Layer t (t = 0..d-1) has a permutation dest[t] of range(p) and a voltage
# vol[t][i] in G. Dart (t, i) joins A_{i,x} to B_{dest[t][i], x * vol[t][i]}.
# Every A and every B then has d darts, so the lift is d-regular before
# duplicate removal, bipartite, and left multiplication by G is an
# automorphism. Hence checking distances from A_{i,e} and B_{j,e} suffices.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m * k = N and Z_m x|_r Z_k a group."""
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
    """Multiplication table T[x][g] = x * g for the group, cached."""
    key = (N, m, k, r)
    T = _TABLES.get(key)
    if T is None:
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        _TABLES[key] = T
    return T


def _cost(p, N, D, T, dest, vol):
    """Number of ordered (source, vertex) pairs at distance > D, over the 2p sources A_{i,e}, B_{j,e}."""
    V = 2 * p * N
    off = p * N
    adj = [[] for _ in range(V)]
    for dt, vt in zip(dest, vol):
        for i in range(p):
            j = dt[i]
            g = vt[i]
            ai = i * N
            bj = off + j * N
            for x in range(N):
                a = ai + x
                b = bj + T[x][g]
                adj[a].append(b)
                adj[b].append(a)
    bad = 0
    sources = [i * N for i in range(p)] + [off + j * N for j in range(p)]
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        bad += V - cnt
    return bad


def _anneal(p, N, d, D, T, rng, iters, deadline):
    """Simulated annealing over permutations and voltages. Returns (dest, vol) with zero cost, or None."""
    dest = []
    vol = []
    for t in range(d):
        perm = list(range(p))
        if t:
            rng.shuffle(perm)
        dest.append(perm)
        vol.append([rng.randrange(N) for _ in range(p)])
    cur = _cost(p, N, D, T, dest, vol)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = 0.3 + 6.0 * (1.0 - it / iters)
        t = rng.randrange(d)
        if p > 1 and rng.random() < 0.2:
            # Swap the destinations of two sources within layer t (stays a permutation).
            i1, i2 = rng.sample(range(p), 2)
            dt = dest[t]
            dt[i1], dt[i2] = dt[i2], dt[i1]
            new = _cost(p, N, D, T, dest, vol)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                dt[i1], dt[i2] = dt[i2], dt[i1]
        else:
            i = rng.randrange(p)
            old = vol[t][i]
            g = rng.randrange(N)
            if g == old:
                continue
            vol[t][i] = g
            new = _cost(p, N, D, T, dest, vol)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                vol[t][i] = old
    if cur == 0:
        return dest, vol
    return None


def _attempt(p, N, d, D, rng, deadline):
    """Random restarts over groups of order N until a zero-cost lift is found or time runs out."""
    groups = _groups(N)
    if not groups:
        return None
    while time.monotonic() < deadline:
        m, k, r = rng.choice(groups)
        T = _table(N, m, k, r)
        res = _anneal(p, N, d, D, T, rng, ITER, deadline)
        if res is not None:
            return T, res[0], res[1]
    return None


def _graph(p, N, d, T, dest, vol):
    """Build the lift as (n, edges), with duplicate edges removed."""
    off = p * N
    edges = set()
    for t in range(d):
        for i in range(p):
            j = dest[t][i]
            g = vol[t][i]
            for x in range(N):
                edges.add((i * N + x, off + j * N + T[x][g]))
    return 2 * p * N, sorted(edges)


def _candidates(lo, hi):
    """(order, p, N) triples with order = 2*p*N even in [lo, hi], ascending by order."""
    cands = []
    start = lo + (lo % 2)
    for M in range(start, hi + 1, 2):
        half = M // 2
        for p in range(1, min(MAX_P, half) + 1):
            if half % p == 0 and half // p >= 2:
                cands.append((M, p, half // p))
        if len(cands) >= MAX_CANDS:
            break
    return cands[:MAX_CANDS]


def _search(d, D, rng, best, deadline):
    """Climb through candidate orders above the current best, doubling budgets per pass."""
    mb = lib._moore_bound(d, D)
    lo = max(best[0] + 1, int(0.45 * mb))
    cands = _candidates(lo, mb)
    budget = 1.0
    while cands and time.monotonic() < deadline:
        cands = [c for c in cands if c[0] > best[0]]
        for M, p, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            if M <= best[0]:
                continue
            res = _attempt(p, N, d, D, rng, min(deadline, now + budget))
            if res is not None:
                T, dest, vol = res
                n, e = _graph(p, N, d, T, dest, vol)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best[0], best[1] = n, e
        budget *= 2.0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Exact record-matching construction for D = 3.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best[0], best[1]

    # Safe baselines.
    if D >= 2 and d >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Bold search: bipartite voltage lifts with p base vertices per side.
    if d >= 2 and D >= 2 and time.monotonic() < deadline:
        _search(d, D, rng, best, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
