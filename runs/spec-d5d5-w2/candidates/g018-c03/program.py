import itertools
import math
import random
import time

import lib

ITERS_CAP = 4000              # max annealing steps per attempt
T_HOT = 1.5                   # initial temperature (unreached-pair units)
T_COLD = 0.15                 # final temperature
ATTEMPT_SECONDS = 4.0         # wall-clock budget per (base size, group) attempt
BASE_SIZES = (2, 3, 4, 1)     # base vertices per side for the new voltage lifts
DUP_PENALTY = 10 ** 6         # cost added per duplicate dart (keeps the graph simple)

_TABLE_CACHE = {}


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
# NEW: multi-orbit voltage lifts with a circulant base graph.
#
# Base graph: a "A" vertices A_0..A_{a-1} and a "B" vertices B_0..B_{a-1}.
# For each i, dart t (t = 0..d-1) joins A_i to B_{(i+t) mod a} with a voltage
# V[i][t] in a finite group G of order N. The lift has 2aN vertices:
#   A(i, x) = i*N + x,   B(j, y) = a*N + j*N + y,
# and dart (i, t) joins A(i, x) to B(j, x * V[i][t]) for all x in G.
# Every vertex has degree d (each B_j receives exactly d darts). For a = 1 this
# is the bi-Cayley graph of the earlier search; a >= 2 gives 2a orbits.
#
# Left multiplication by h is an automorphism of the lift, so distances from
# any vertex equal distances from one representative of its orbit. Therefore the
# diameter test needs only 2a BFS runs (one per base vertex, from its identity).
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


def _group_tables(N, m, k, r):
    """Multiplication table mt[x][g] = x*g and inverse list for Z_m x|_r Z_k (cached)."""
    key = (m, k, r)
    if key not in _TABLE_CACHE:
        if len(_TABLE_CACHE) > 16:
            _TABLE_CACHE.clear()
        _, mul, inv = lib.semidirect_group(m, k, r)
        mt = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        _TABLE_CACHE[key] = (mt, invs)
    return _TABLE_CACHE[key]


def _dup_count(a, d, V):
    """Number of repeated (base neighbour, voltage) pairs; each one would create a parallel edge."""
    total = 0
    for i in range(a):
        seen = set()
        for t in range(d):
            key = ((i + t) % a, V[i][t])
            if key in seen:
                total += 1
            else:
                seen.add(key)
    return total


def _lift_adj(a, N, d, mt, V):
    """Adjacency lists of the voltage lift described above."""
    n = 2 * a * N
    adj = [[] for _ in range(n)]
    b0 = a * N
    for i in range(a):
        for t in range(d):
            j = (i + t) % a
            g = V[i][t]
            off = b0 + j * N
            for x in range(N):
                u = i * N + x
                w = off + mt[x][g]
                adj[u].append(w)
                adj[w].append(u)
    return n, adj


def _unreached_total(n, adj, sources, D):
    """Sum over sources of the number of vertices not within distance D of the source."""
    total = 0
    for s in sources:
        seen = bytearray(n)
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
        total += n - cnt
    return total


def _cost(a, N, d, D, mt, V):
    """Zero iff the lift is simple and has diameter <= D (connected included)."""
    dups = _dup_count(a, d, V)
    if dups:
        return DUP_PENALTY + dups
    n, adj = _lift_adj(a, N, d, mt, V)
    sources = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    return _unreached_total(n, adj, sources, D)


def _anneal(a, N, d, D, mt, rng, deadline, iters):
    """Simulated annealing over the a*d voltages; returns V with cost 0, or None."""
    V = [[rng.randrange(N) for _ in range(d)] for _ in range(a)]
    cur = _cost(a, N, d, D, mt, V)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(a)
        t = rng.randrange(d)
        old = V[i][t]
        g = rng.randrange(N)
        if g == old:
            continue
        V[i][t] = g
        c = _cost(a, N, d, D, mt, V)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            V[i][t] = old
    return V if cur == 0 else None


def _edges_from(a, N, d, mt, V):
    """Explicit (n, edges) of the lift with voltages V."""
    edges = []
    for i in range(a):
        for t in range(d):
            j = (i + t) % a
            g = V[i][t]
            off = a * N + j * N
            for x in range(N):
                edges.append((i * N + x, off + mt[x][g]))
    return 2 * a * N, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
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

    moore = lib._moore_bound(d, D)
    a_idx = 0

    while time.monotonic() < deadline:
        # Base sizes a for which the next order (just above the current best) is still
        # below the Moore bound.
        avail = [a for a in BASE_SIZES if 2 * a * (best_n // (2 * a) + 1) <= moore]
        if not avail:
            break
        a = avail[a_idx % len(avail)]
        a_idx += 1
        N = best_n // (2 * a) + 1

        groups = _groups(N)
        m, k, r = rng.choice(groups)
        mt, _ = _group_tables(N, m, k, r)

        att_deadline = min(deadline, time.monotonic() + ATTEMPT_SECONDS)
        V = _anneal(a, N, d, D, mt, rng, att_deadline, ITERS_CAP)
        if V is not None:
            n, e = _edges_from(a, N, d, mt, V)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
