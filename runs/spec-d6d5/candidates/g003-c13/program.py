"""Tabu search over voltage lifts with a new move set and group enumeration.

New in this version:
  * _groups_of_order(G): deterministic enumeration of all semidirect products
    Z_m x| Z_k of a given order G (cached), replacing random group sampling.
  * _tabu(...): tabu search that evaluates a sampled neighbourhood each step,
    applies the best non-tabu move (even if worse), and keeps the best state.
    Moves are voltage changes and, for k >= 2, swaps of two B-targets inside
    one layer, which rewires the base graph while keeping every degree at d.
  * Early stop when the Moore bound is reached (e.g. d=3, D=3 returns at once).
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group enumeration.
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _groups_of_order(G):
    """All semidirect products Z_m x| Z_k2 of order G, as (order, mul) pairs. Cached."""
    if G in _GROUP_CACHE:
        return _GROUP_CACHE[G]
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m == 1:
            rs = [0]
        else:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        for r in rs:
            try:
                order, mul, _ = lib.semidirect_group(m, k2, r)
            except ValueError:
                continue
            out.append((order, mul))
            if len(out) >= 300:
                break
        if len(out) >= 300:
            break
    _GROUP_CACHE[G] = out
    return out


# ----------------------------------------------------------------------------
# Voltage-lift evaluation.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h. Dart (i, j, s) joins
# A_i,g to B_j,g*s. Left multiplication is an automorphism, so the graph has
# diameter <= D iff a BFS of depth D from each of the 2k representatives
# reaches every vertex.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Tabu search over voltages and base-graph layer swaps.
# ----------------------------------------------------------------------------

def _tabu(d, D, k, G, mul, rng, iters, deadline, cache):
    """Tabu search: each step evaluates a sampled neighbourhood and applies the best
    non-tabu move, even if it is worse. Returns (n, edges) with diameter <= D, or None."""

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [perm(x[2]) for x in darts]
    cur = _cost(k, G, D, darts, perms)
    best = cur
    best_state = ([list(x) for x in darts], list(perms))
    tabu = {}
    tenure = 7

    for t in range(iters):
        if best == 0 or time.monotonic() > deadline:
            break
        move = None
        move_cost = None
        move_key = None
        for _ in range(12):
            if k == 1 or rng.random() < 0.7:
                idx = rng.randrange(len(darts))
                old_s = darts[idx][2]
                new_s = rng.randrange(G)
                if new_s == old_s:
                    continue
                key = ('v', idx)
                if tabu.get(key, -1) > t:
                    continue
                old_p = perms[idx]
                darts[idx][2] = new_s
                perms[idx] = perm(new_s)
                c = _cost(k, G, D, darts, perms)
                darts[idx][2] = old_s
                perms[idx] = old_p
                mv = ('v', idx, new_s)
            else:
                L = rng.randrange(d)
                a, b = rng.sample(range(k), 2)
                ia, ib = L * k + a, L * k + b
                key = ('s', L)
                if tabu.get(key, -1) > t:
                    continue
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                c = _cost(k, G, D, darts, perms)
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                mv = ('s', ia, ib)
            if move_cost is None or c < move_cost:
                move_cost = c
                move = mv
                move_key = key
        if move is None:
            continue
        if move[0] == 'v':
            _, idx, new_s = move
            darts[idx][2] = new_s
            perms[idx] = perm(new_s)
        else:
            _, ia, ib = move
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        cur = move_cost
        tabu[move_key] = t + tenure
        if cur < best:
            best = cur
            best_state = ([list(x) for x in darts], list(perms))

    if best == 0:
        return _edges(k, G, best_state[0], best_state[1])
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    caches = {}
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice([1, 1, 1, 2])
        base = best_n // (2 * k)
        G = base + 1 + rng.randrange(0, 3)
        groups = _groups_of_order(G)
        if not groups:
            continue
        order, mul = rng.choice(groups)
        cache = caches.setdefault((order, id(mul)), {})
        res = _tabu(d, D, k, order, mul, rng, 600, deadline, cache)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
