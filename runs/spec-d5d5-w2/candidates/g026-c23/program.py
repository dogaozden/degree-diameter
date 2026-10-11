import math
import random
import time

import lib

ANNEAL_ITERS = 400      # annealing steps per (group, base graph) try
T_HOT = 4.0             # initial temperature (unreached-pair units)
T_COLD = 0.2            # final temperature
MAX_GROUPS = 6          # groups tried per (b, N) attempt
B_MAX = 6               # largest base-graph side size b (b vertices per side)
W0 = 10                 # initial window of totals above the current best
W_MAX = 60              # widest window allowed


# ----------------------------------------------------------------------------
# Baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group-voltage lifts of small bipartite base graphs.
#
# Base graph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}. Each A_i has
# exactly d darts (A_i, B_j, g) with a voltage g in a finite group G of order N.
# Each B_j receives exactly d darts overall. The lift has vertices (A_i, x) and
# (B_j, y), x, y in G, and edges (A_i, x) -- (B_j, x*g) for every dart.
#
# Left multiplication by G is an automorphism of the lift, so the diameter is
# the maximum eccentricity over the 2b representatives (A_i, e) and (B_j, e).
# Total order is 2*b*N, which is a generalisation of the bi-Cayley search
# (b = 1). Groups are semidirect products Z_m x| Z_k.
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


def _mul_table(N, m, k, r):
    """Multiplication table M[x][g] = x*g for the semidirect group; identity is 0."""
    _, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(x, g) for g in range(N)] for x in range(N)]


def _valid_darts(d, bpos, vol):
    """Reject duplicate darts (same A vertex, same B vertex, same voltage)."""
    seen = set()
    for p in range(len(bpos)):
        t = (p // d, bpos[p], vol[p])
        if t in seen:
            return False
        seen.add(t)
    return True


def _adjacency(N, b, d, M, bpos, vol):
    """Adjacency lists of the lift. A-vertex (i, x) -> i*N + x; B-vertex (j, y) -> (b+j)*N + y."""
    V = 2 * b * N
    adj = [[] for _ in range(V)]
    for p in range(b * d):
        base_u = (p // d) * N
        base_v = (b + bpos[p]) * N
        g = vol[p]
        for x in range(N):
            u = base_u + x
            v = base_v + M[x][g]
            adj[u].append(v)
            adj[v].append(u)
    return adj, V


def _cost(N, b, d, D, M, bpos, vol):
    """Total number of (representative, vertex) pairs not within distance D."""
    adj, V = _adjacency(N, b, d, M, bpos, vol)
    sources = [i * N for i in range(b)] + [(b + j) * N for j in range(b)]
    total = 0
    for s in sources:
        seen = bytearray(V)
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
        total += V - cnt
    return total


def _anneal(N, b, d, D, M, rng, iters, deadline):
    """Anneal the B-endpoints and voltages of the darts until the diameter is <= D."""
    P = b * d
    bpos = [j for j in range(b) for _ in range(d)]
    rng.shuffle(bpos)
    vol = [rng.randrange(N) for _ in range(P)]
    for _ in range(200):
        if _valid_darts(d, bpos, vol):
            break
        vol = [rng.randrange(N) for _ in range(P)]
    else:
        return None
    cur = _cost(N, b, d, D, M, bpos, vol)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        nb, nv = bpos[:], vol[:]
        if rng.random() < 0.5:
            p = rng.randrange(P)
            q = rng.randrange(P)
            if nb[p] == nb[q]:
                continue
            nb[p], nb[q] = nb[q], nb[p]      # keeps every B-degree at d
        else:
            p = rng.randrange(P)
            nv[p] = rng.randrange(N)
        if not _valid_darts(d, nb, nv):
            continue
        c = _cost(N, b, d, D, M, nb, nv)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            bpos, vol, cur = nb, nv, c
    if cur == 0:
        return bpos, vol
    return None


def _attempt(N, b, d, D, rng, deadline):
    """Try several groups of order N for a base graph with b vertices per side."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        M = _mul_table(N, m, k, r)
        res = _anneal(N, b, d, D, M, rng, ANNEAL_ITERS, deadline)
        if res is not None:
            bpos, vol = res
            return M, bpos, vol
    return None


def _lift_edges(N, b, d, M, bpos, vol):
    """Edge list and order of the lift."""
    edges = []
    for p in range(b * d):
        u_base = (p // d) * N
        v_base = (b + bpos[p]) * N
        g = vol[p]
        for x in range(N):
            edges.append((u_base + x, v_base + M[x][g]))
    return 2 * b * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Fast baselines.
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    Mo = lib.moore_bound(d, D)
    W = W0
    budget = 1.5
    fails = 0

    # Search for lifts whose total order beats the current best. Targets are
    # drawn from a window just above the best so that small wins come quickly.
    while time.monotonic() < deadline:
        bt = best[0]
        if bt >= Mo:
            break
        cands = []
        for b in range(1, B_MAX + 1):
            lo = max(d, -(-(bt + 1) // (2 * b)))
            hi = min(Mo // (2 * b), (bt + W) // (2 * b))
            for N in range(lo, hi + 1):
                cands.append((b, N))
        if not cands:
            W = min(W + 4, W_MAX)
            continue
        b, N = rng.choice(cands)
        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt(N, b, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            if fails % 8 == 0:
                W = min(W + 4, W_MAX)
                budget = min(budget * 1.3, 6.0)
            continue
        M, bpos, vol = res
        n, edges = _lift_edges(N, b, d, M, bpos, vol)
        consider(n, edges)
        fails = 0
        W = W0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
