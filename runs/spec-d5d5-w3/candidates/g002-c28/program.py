import itertools
import math
import random
import time

import lib

MAX_K = 5            # base-graph size: k A-vertices and k B-vertices (k = 1 is bi-Cayley)
MAX_GROUPS = 25      # groups tried per (k, N) attempt
RESTARTS = 3         # annealing restarts per group
ITERS = 1500         # annealing steps per restart
BIG = 1000           # penalty per duplicate (i, j, g) dart
WINDOW = 8           # candidate (V, k, N) triples attempted per round


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
# Multi-orbit group lifts ("dart" search).
#
# Base graph: k A-vertices and k B-vertices, each of degree d (bipartite).
# Over a group G of order N, a dart t = (i, j, g) lifts to the edges
#     A_{i,x} -- B_{j, x*g}   for every x in G.
# Left multiplication is an automorphism, so eccentricities need only be checked
# from the 2k orbit representatives A_{i,e} and B_{j,e}.
#
# Each A-vertex gets exactly d darts; each B-vertex receives exactly d darts
# (J is a shuffled multiset with every j repeated d times). Annealing moves are
# either re-drawing a group label g or swapping two darts' target j. The cost
# is the number of pairs at distance > D from the representatives, plus a
# penalty for duplicate (j, g) darts under the same i (which would create
# multi-edges).
#
# k = 1 is the bi-Cayley search; k >= 2 gives a larger, more flexible search
# space at the same vertex count 2kN.
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


def _tables(m, k, r):
    """Return (N, T, invs) for the group Z_m x|_r Z_k, with T[x][g] = x*g."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    return order, T, invs


def _cost(k, N, d, D, T, invs, J, G):
    """Unreached (source, vertex) pairs from orbit representatives, plus duplicate-dart penalty."""
    kN = k * N
    V = 2 * kN
    kd = k * d
    adjA = [[(J[t], G[t]) for t in range(i * d, (i + 1) * d)] for i in range(k)]
    adjB = [[] for _ in range(k)]
    for t in range(kd):
        adjB[J[t]].append((t // d, invs[G[t]]))
    dup = 0
    for i in range(k):
        dup += d - len(set(adjA[i]))

    unreached = 0
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in adjA[i]:
                        v = kN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, h in adjB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        unreached += V - cnt
    return unreached + BIG * dup


def _anneal(k, N, d, D, T, invs, rng, iters, deadline):
    """Anneal darts (J, G) to zero cost. Returns (J, G) or None."""
    kd = k * d
    J = [j for j in range(k) for _ in range(d)]
    rng.shuffle(J)
    G = [rng.randrange(N) for _ in range(kd)]
    cur = _cost(k, N, d, D, T, invs, J, G)
    for it in range(iters):
        if cur == 0:
            return J, G
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if rng.random() < 0.5:
            t = rng.randrange(kd)
            old = G[t]
            G[t] = rng.randrange(N)
            v = _cost(k, N, d, D, T, invs, J, G)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                G[t] = old
        else:
            t1 = rng.randrange(kd)
            t2 = rng.randrange(kd)
            if J[t1] == J[t2]:
                continue
            J[t1], J[t2] = J[t2], J[t1]
            v = _cost(k, N, d, D, T, invs, J, G)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                J[t1], J[t2] = J[t2], J[t1]
    if cur == 0:
        return J, G
    return None


def _attempt(k, N, d, D, rng, deadline):
    """Try several groups of order N for base size k; return (k, N, T, J, G) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, T, invs = _tables(m, kk, r)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            res = _anneal(k, order, d, D, T, invs, rng, ITERS, deadline)
            if res is not None:
                J, G = res
                return (k, order, T, J, G)
    return None


def _graph_from(k, N, d, T, J, G):
    """Expand darts into the explicit lifted graph on 2kN vertices."""
    kN = k * N
    edges = []
    for t in range(k * d):
        i = t // d
        j = J[t]
        g = G[t]
        for x in range(N):
            edges.append((i * N + x, kN + j * N + T[x][g]))
    return 2 * kN, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    deadline = start + max(0.5, min(0.85 * tl, tl - 3.0))
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

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # Baselines (instant).
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

    if d < 2:
        return best

    # Candidate orders V = 2kN above the current best, ascending.
    Vmax = lib.moore_bound(d, D)
    cands = []
    for k in range(1, MAX_K + 1):
        for N in range(max(2, (d + k - 1) // k), Vmax // (2 * k) + 1):
            V = 2 * k * N
            if best_n < V <= Vmax:
                cands.append((V, k, N))
    cands.sort()

    dead = set()
    budget = 0.5
    while time.monotonic() < deadline:
        live = [c for c in cands if c not in dead and c[0] > best_n]
        if not live:
            break
        progressed = False
        for V, k, N in live[:WINDOW]:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(k, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            kk, NN, T, J, G = res
            n, e = _graph_from(kk, NN, d, T, J, G)
            if lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
                progressed = True
                break
            dead.add((V, k, N))
        if not progressed:
            budget *= 1.6

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
