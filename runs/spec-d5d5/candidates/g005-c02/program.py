"""Voltage lifts of a 4-vertex bipartite base graph over semidirect products Z_m x| Z_k.

New construction (not in the parent): base graph with two A-vertices A0, A1 and two
B-vertices B0, B1. Each A_u has exactly d darts and each B_v has exactly d darts, so the
dart multiplicities are [[a, d-a], [d-a, a]] for some 1 <= a <= d-1. Every dart carries a
group voltage g, and the lift joins (A_u, x) to (B_v, x*g). The lift has 4N vertices, is
bipartite by construction, and has degree d.

Reduction used for the diameter check: left multiplication by a group element is an
automorphism of the lift, so the distance from (u, x) to (w, y) equals the distance from
(u, e) to (w, x^-1 y). Hence it suffices to run BFS from the four identity vertices
(A0,e), (A1,e), (B0,e), (B1,e). Zero unreached pairs from those four sources means the
diameter is at most D.

Annealing moves single voltages inside a dart class (voltages within a class stay distinct,
so the lift is simple). The search sweeps group orders N upward from the current record
and keeps the largest valid lift.
"""
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 10
ITERS = 300
MARGIN_S = 3.0

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
    """Cached multiplication table T[x][g] = x*g and inverse table INV[g]."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is None:
        N = m * k
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        INV = [inv(g) for g in range(N)]
        hit = (T, INV)
        _TABLE_CACHE[key] = hit
    return hit


def _cost(N, T, INV, classes, D):
    """Total number of (source, vertex) pairs at distance > D, over the four identity sources."""
    c00, c01, c10, c11 = classes
    # Vertex ids: A_u,x = u*N + x (u in {0,1}); B_v,y = 2N + v*N + y.
    outs = (
        [(2 * N, g) for g in c00] + [(3 * N, g) for g in c01],   # darts out of A_0
        [(2 * N, g) for g in c10] + [(3 * N, g) for g in c11],   # darts out of A_1
    )
    intos = (
        [(0, INV[g]) for g in c00] + [(N, INV[g]) for g in c10],  # darts into B_0
        [(0, INV[g]) for g in c01] + [(N, INV[g]) for g in c11],  # darts into B_1
    )
    V = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                if w < 2 * N:
                    u = 1 if w >= N else 0
                    Tx = T[w - u * N]
                    for tb, g in outs[u]:
                        z = tb + Tx[g]
                        if not seen[z]:
                            seen[z] = 1
                            nxt.append(z)
                else:
                    w2 = w - 2 * N
                    v = 1 if w2 >= N else 0
                    Ty = T[w2 - v * N]
                    for sb, gi in intos[v]:
                        z = sb + Ty[gi]
                        if not seen[z]:
                            seen[z] = 1
                            nxt.append(z)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(N, T, INV, d, D, rng, iters, deadline):
    """Anneal the four dart classes so that all pairs are within distance D."""
    a = rng.randint(1, d - 1)
    sizes = [a, d - a, d - a, a]
    classes = [rng.sample(range(N), s) for s in sizes]
    cur = _cost(N, T, INV, classes, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        c = rng.randrange(4)
        cl = classes[c]
        i = rng.randrange(len(cl))
        g = rng.randrange(N)
        if g in cl:
            continue
        old = cl[i]
        cl[i] = g
        v = _cost(N, T, INV, classes, D)
        temp = max(0.05, 3.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            cl[i] = old
    return classes if cur == 0 else None


def _edges(N, T, classes):
    """Edge list of the 4N-vertex lift."""
    c00, c01, c10, c11 = classes
    spec = ((0, 2 * N, c00), (0, 3 * N, c01), (N, 2 * N, c10), (N, 3 * N, c11))
    edges = []
    for ub, vb, cls in spec:
        for g in cls:
            for x in range(N):
                edges.append((ub + x, vb + T[x][g]))
    return edges


def _attempt(N, d, D, rng, deadline):
    """Try several groups of order N; return an edge list for a valid 4N-vertex lift, or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() >= deadline:
            return None
        T, INV = _tables(m, k, r)
        classes = _anneal(N, T, INV, d, D, rng, ITERS, deadline)
        if classes is not None:
            return _edges(N, T, classes)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    avail = max(0.0, min(0.8 * time_limit, time_limit - MARGIN_S))
    deadline = start + avail
    rng = random.Random(seed)

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        consider(2, [(0, 1)])
        return best

    # Calibration case: incidence graph of PG(2, d-1) meets the Moore bound.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        if lib.is_prime_power(d - 1):
            return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))

    # Bipartite Moore bound caps the order, so 4N <= bound.
    Nmax = lib._moore_bound(d, D) // 4
    lo = max(d, best_n // 4 + 1)
    hi = Nmax
    budget = 0.4
    while lo <= hi and time.monotonic() < deadline:
        found = False
        for N in range(lo, hi + 1):
            if N < lo:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            edges = _attempt(N, d, D, rng, min(deadline, now + budget))
            if edges is None:
                continue
            consider(4 * N, edges)
            lo = max(lo, N + 1)
            found = True
        if not found:
            budget = min(budget * 2, 8.0)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
