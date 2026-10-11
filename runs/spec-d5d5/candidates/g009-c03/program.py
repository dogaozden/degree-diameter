import math
import random
import time

import lib

T_HOT = 2.0       # initial annealing temperature (unreached-pair units)
T_COLD = 0.2      # final annealing temperature
BIG = 10 ** 6     # penalty for duplicate voltage triples (would create duplicate edges)
ITERS = 1500      # annealing steps per attempt
B_CHOICES = (2, 2, 3, 4, 1)  # base-graph sizes per side; 2+ is the bold, non-bi-Cayley part

_GROUP_CACHE = {}


# ----------------------------------------------------------------------------
# Safe baseline families (always checked with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect groups Z_m x| Z_k of order N.
#
# Base graph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}, with d
# "darts" per A-vertex. Dart (k, i) joins A_i to B_{perm_k[i]} with voltage h.
# The base graph is d-regular bipartite (each perm_k is a permutation), so every
# lift vertex has degree d. Lift vertices are (side, x) with x in G, and
#   (A_i, x) ~ (B_j, x*h)   for every dart (i, j, h).
# Left multiplication by G is an automorphism, so only the 2b fibre
# representatives (s, identity) need BFS.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, for Z_m x|_r Z_k."""
    if N in _GROUP_CACHE:
        return _GROUP_CACHE[N]
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUP_CACHE[N] = out
    return out


def _cost(b, N, D, T, perms, vol, d):
    """Total number of (fibre representative, vertex) pairs not within distance D.

    Returns BIG if two darts share the same (i, j, h), which would create a
    duplicate edge.
    """
    V = 2 * b * N
    adj = [[] for _ in range(V)]
    seen_dart = set()
    for k in range(d):
        pk = perms[k]
        for i in range(b):
            j = pk[i]
            h = vol[k * b + i]
            key = (i, j, h)
            if key in seen_dart:
                return BIG
            seen_dart.add(key)
            base_a = i * N
            base_b = (b + j) * N
            for x in range(N):
                a = base_a + x
                c = base_b + T[x][h]
                adj[a].append(c)
                adj[c].append(a)
    total = 0
    for s in range(2 * b):
        src = s * N  # fibre representative: group identity is index 0
        seen = bytearray(V)
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
            if cnt == V:
                break
        total += V - cnt
    return total


def _anneal(b, N, D, T, perms, d, rng, deadline):
    """Anneal the voltages (one per dart) to zero unreached pairs; return voltages or None."""
    L = d * b
    vol = [rng.randrange(N) for _ in range(L)]
    cur = _cost(b, N, D, T, perms, vol, d)
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        q = rng.randrange(L)
        h = rng.randrange(N)
        old = vol[q]
        if h == old:
            continue
        vol[q] = h
        v = _cost(b, N, D, T, perms, vol, d)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vol[q] = old
    return vol if cur == 0 else None


def _edges(b, N, perms, vol, d, T):
    """Return (vertex_count, edge list) of the lift described by the voltages."""
    edges = []
    for k in range(d):
        for i in range(b):
            j = perms[k][i]
            h = vol[k * b + i]
            for x in range(N):
                edges.append((i * N + x, (b + j) * N + T[x][h]))
    return 2 * b * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

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

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    consider(*lib.haar_graph(d, range(d)))

    if D == 3:
        if d >= 2 and lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
            return best
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    rng = random.Random(seed)
    bound = lib._moore_bound(d, D)
    budget = 2.0
    fails = 0

    while time.monotonic() < deadline:
        options = []
        for b in (1, 2, 3, 4):
            lo = best_n // (2 * b) + 1
            hi = bound // (2 * b)
            if lo < 2:
                lo = 2
            if lo <= hi:
                options.append((b, lo, hi))
        if not options:
            break

        b, lo, hi = rng.choice([o for o in options if o[0] in B_CHOICES] or options)
        N = rng.randint(lo, min(hi, lo + 3))
        groups = _groups(N)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]

        perms = []
        for _ in range(d):
            if b == 1:
                perms.append([0])
            else:
                p = list(range(b))
                rng.shuffle(p)
                perms.append(p)

        att_deadline = min(deadline, time.monotonic() + budget)
        vol = _anneal(b, N, D, T, perms, d, rng, att_deadline)
        if vol is None:
            fails += 1
            if fails % 5 == 0:
                budget = min(budget * 1.5, 12.0)
            continue

        n, edges = _edges(b, N, perms, vol, d, T)
        before = best_n
        consider(n, edges)
        if best_n > before:
            fails = 0
            budget = 2.0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
