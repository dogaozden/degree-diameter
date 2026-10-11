import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Shared group utilities.
# ----------------------------------------------------------------------------

def _divisors(G):
    """Divisors k of G with G // k >= 2 (the possible Z_k order of a semidirect Z_m x| Z_k)."""
    return [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]


def _sample_group(G, rng, choices):
    """Random semidirect product Z_m x| Z_k of exact order G; returns (order, mul, inv) or None."""
    if not choices:
        return None
    for _ in range(80):
        k2 = rng.choice(choices)
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul, inv
    return None


def _make_pairs(G, mul, inv):
    """Cached pair(s) -> (f, b) with f[x] = x*s and b[x] = x*s^{-1} as permutations of the group."""
    cache = {}

    def pair(s):
        p = cache.get(s)
        if p is None:
            p = ([mul(g, s) for g in range(G)], [mul(g, inv(s)) for g in range(G)])
            cache[s] = p
        return p

    return pair


# ----------------------------------------------------------------------------
# Haar graphs over groups.
#
# A_x ~ B_{x*s} for s in S. Left multiplication is transitive on each side, so
# diameter <= D iff BFS from A_e and from B_e reaches everything within D.
#
# New routine: greedy connection-set construction. S is grown one element at a
# time, each time choosing the candidate (from a random pool) that minimises the
# number of unreached (source, vertex) pairs. The hill-climb then starts from
# this greedy set instead of a random one, and restarts draw fresh greedy sets.
# ----------------------------------------------------------------------------

def _reach_bad(G, pairs, D):
    """Number of (source, vertex) pairs not reached within D steps from A_e and from B_e."""
    N = 2 * G
    bad = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for f, _b in pairs:
                        v = G + f[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for _f, b in pairs:
                        v = b[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        bad += N - cnt
    return bad


def _greedy_start(G, d, D, pair, rng, deadline, pool_size=30):
    """Grow S greedily: at each step add the pool element minimising the reach-deficit."""
    S = []
    while len(S) < d:
        if time.monotonic() > deadline:
            return None
        pool = [x for x in rng.sample(range(G), min(pool_size, G)) if x not in S]
        best_x, best_c = None, None
        for x in pool:
            c = _reach_bad(G, [pair(s) for s in S + [x]], D)
            if best_c is None or c < best_c:
                best_x, best_c = x, c
        if best_x is None:
            return None
        S.append(best_x)
    return S


def _climb(G, d, D, pair, rng, deadline, S):
    """Hill-climb S (|S| = d) to zero deficit. Returns S, or None on timeout or stagnation."""
    def cost(T):
        return _reach_bad(G, [pair(s) for s in T], D)

    c = cost(S)
    stale = 0
    while c > 0:
        if time.monotonic() > deadline or stale > 300:
            return None
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            stale += 1
            continue
        T = S[:]
        T[i] = x
        ct = cost(T)
        if ct <= c or rng.random() < 0.03:
            if ct < c:
                stale = 0
            else:
                stale += 1
            S, c = T, ct
        else:
            stale += 1
    return S


def _haar_search(d, D, seed, deadline, lo):
    """Search Haar graphs over groups of order >= lo; return the largest valid (n, edges) or None."""
    rng = random.Random(seed * 1000003 + 17)
    best = None
    while time.monotonic() < deadline - 0.3:
        span = max(3, lo // 60)
        G = rng.randint(lo, lo + span)
        grp = _sample_group(G, rng, _divisors(G))
        if grp is None:
            lo += 1
            continue
        order, mul, inv = grp
        pair = _make_pairs(order, mul, inv)
        attempt_deadline = min(deadline, time.monotonic() + 5.0)
        S = None
        while S is None and time.monotonic() < attempt_deadline:
            start = _greedy_start(order, d, D, pair, rng, attempt_deadline)
            if start is None:
                break
            S = _climb(order, d, D, pair, rng, attempt_deadline, start)
        if S is None:
            continue
        edges = [(g, order + mul(g, s)) for g in range(order) for s in S]
        n = 2 * order
        if lib.is_valid(n, edges, d, D):
            if best is None or n > best[0]:
                best = (n, edges)
            lo = order + 1
    return best


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts with k base vertices per side, annealed.
#
# A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h. Dart (i, j, s) joins A_{i,g} to
# B_{j, g*s}. Left multiplication acts on each block, so BFS from one A and one
# B representative per block suffices.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _bi_cost(k, G, D, darts, perms, limit):
    """Unreached (representative, vertex) pairs. Zero iff valid. Exits early above limit."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
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
        if total > limit:
            return total
    return total


def _bi_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments. Returns (darts, perms, cost)."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_perm(mul, G, s) for _, _, s in darts]
    cost = _bi_cost(k, G, D, darts, perms, float("inf"))

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _perm(mul, G, new_s)
            c2 = _bi_cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _bi_cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, perms, cost


def _anneal_search(d, D, seed, deadline, best_n):
    """Anneal bi-Cayley lifts with k in {2,3,4} base vertices per side; return best valid or None."""
    rng = random.Random(seed * 7919 + 5)
    best = None
    while time.monotonic() < deadline - 0.3:
        k = rng.choice([2, 2, 3, 4])
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(3, lo // 8)
        G = rng.randint(lo, hi)
        grp = _sample_group(G, rng, _divisors(G))
        if grp is None:
            continue
        order, mul, _inv = grp
        adeadline = min(deadline, time.monotonic() + 6.0)
        darts, perms, c = _anneal(d, D, k, order, mul, rng, adeadline, 400)
        if c == 0:
            n, e = _bi_edges(k, order, darts, perms)
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
    return best


# ----------------------------------------------------------------------------
# Projective-plane base (diameter 3, used for small D and calibration).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    if D >= 5 and d >= 4:
        moore = lib._moore_bound(d, D)
        lo = max(4, (moore // 2) * 43 // 100)
        try:
            h = _haar_search(d, D, seed, t0 + 0.5 * total, lo)
            if h is not None and h[0] > best[0] and lib.is_valid(h[0], h[1], d, D):
                best = h
        except Exception:
            pass
        try:
            a = _anneal_search(d, D, seed, t0 + total, best[0])
            if a is not None and a[0] > best[0] and lib.is_valid(a[0], a[1], d, D):
                best = a
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
