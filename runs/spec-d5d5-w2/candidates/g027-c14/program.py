import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Search parameters for the voltage-lift search.
# A lift has k "A" base vertices and k "B" base vertices, d layers of darts.
# Layer t joins A_i to B_{sigma_t(i)} with voltage g_{t,i} in a finite group G
# of order N, so the lift has 2*k*N vertices and is d-regular (up to duplicate
# edges, which only lower degree). It is bipartite by construction.
# ----------------------------------------------------------------------------
ITERS = 400           # annealing steps per (group, base structure) attempt
T_HOT = 2.0           # initial temperature, in unreached-pair units
T_COLD = 0.1          # final temperature
MAX_GROUPS = 4        # groups tried per sampled order N
SPREAD = 24           # sample N from a window of this width above the current floor
KMAX = 4              # maximum number of base vertices per side
PERM_MOVE = 0.3       # probability of a permutation move when k > 1


# ----------------------------------------------------------------------------
# Fallback families (fast, validated before use).
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
    for q in range(min(d - 1, 4), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group helpers.
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


# ----------------------------------------------------------------------------
# Voltage-lift evaluation.
#
# Vertex A_{i,x} has index i*N + x; B_{j,y} has index (k + j)*N + y.
# Dart (i, j, g) joins A_{i,x} to B_{j, x*g} for every x in G.
# Left multiplication by h (x -> h*x) is an automorphism of the lift that is
# transitive on each fibre, so distances from the identity vertex of each base
# vertex decide the diameter. Only 2k BFS runs are needed.
# ----------------------------------------------------------------------------

def _adjacency(k, N, T, darts):
    n = 2 * k * N
    adj = [[] for _ in range(n)]
    for i, j, g in darts:
        ba = i * N
        bb = (k + j) * N
        for x in range(N):
            a = ba + x
            b = bb + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _unreached(n, k, N, adj, D):
    """Count (source, vertex) pairs at distance more than D, over the 2k identity sources."""
    total = 0
    for b in range(2 * k):
        src = b * N
        seen = bytearray(n)
        seen[src] = 1
        cnt = 1
        frontier = [src]
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
        total += n - cnt
    return total


def _edges(k, N, T, darts):
    E = set()
    for i, j, g in darts:
        for x in range(N):
            a = i * N + x
            b = (k + j) * N + T[x][g]
            E.add((a, b) if a < b else (b, a))
    return sorted(E)


def _anneal(k, N, T, d, D, rng, deadline):
    """Anneal over permutations sigma_t and voltages g_{t,i} to make the lift have diameter <= D.

    Returns the dart list on success, else None.
    """
    n = 2 * k * N
    sigma = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]

    def cost(sg, vo):
        darts = [(i, sg[t][i], vo[t][i]) for t in range(d) for i in range(k)]
        return _unreached(n, k, N, _adjacency(k, N, T, darts), D), darts

    cur, darts = cost(sigma, volt)
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        sg = [row[:] for row in sigma]
        vo = [row[:] for row in volt]
        t = rng.randrange(d)
        if k > 1 and rng.random() < PERM_MOVE:
            a, b = rng.sample(range(k), 2)
            sg[t][a], sg[t][b] = sg[t][b], sg[t][a]
        else:
            i = rng.randrange(k)
            vo[t][i] = rng.randrange(N)
        v, dd = cost(sg, vo)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sigma, volt, cur, darts = sg, vo, v, dd
    if cur == 0:
        return darts
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
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

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
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

    moore = lib._moore_bound(d, D)

    # Main search: voltage lifts of small base graphs over finite groups.
    # The window of orders starts just above the current best and climbs as
    # better graphs are found.
    while time.monotonic() < deadline:
        valid_k = []
        for k in range(1, KMAX + 1):
            lo = best_n // (2 * k) + 1
            hi = moore // (2 * k)
            if lo <= hi and lo >= 1:
                valid_k.append(k)
        if not valid_k:
            break
        k = rng.choice(valid_k)
        lo = best_n // (2 * k) + 1
        hi = min(moore // (2 * k), lo + SPREAD)
        N = rng.randint(lo, hi)

        groups = _groups(N)
        rng.shuffle(groups)
        for m, kk, r in groups[:MAX_GROUPS]:
            if time.monotonic() >= deadline:
                break
            order, mul, inv = lib.semidirect_group(m, kk, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            darts = _anneal(k, N, T, d, D, rng, deadline)
            if darts is not None:
                consider(2 * k * N, _edges(k, N, T, darts))
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
