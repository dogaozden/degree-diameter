import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Shared state: cur[0] holds the incumbent (n, edges). Every candidate is checked
# with lib.is_valid before it can replace the incumbent, so the output stays valid.
# ----------------------------------------------------------------------------

def _consider(cur, n, e, d, D):
    """Adopt (n, e) as the incumbent if it is strictly larger and valid."""
    if n > cur[0][0] and lib.is_valid(n, e, d, D):
        cur[0] = (n, e)
        return True
    return False


# ----------------------------------------------------------------------------
# Base family 1: projective plane incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Base family 2 (the incumbent-producing family): annealed voltage lifts over
# semidirect products Z_m x| Z_k. Kept as a safety net so the previous level of
# quality is still reached.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
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
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _vcost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D."""
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


def _vedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _vanneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _vcost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


def _voltage_phase(d, D, rng, deadline, cur):
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 2, 2, 3])
        G = max(2, cur[0][0] // (2 * k) + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _vanneal(d, D, k, order, mul, rng, deadline, 800)
        if res is not None:
            _consider(cur, res[0], res[1], d, D)


# ----------------------------------------------------------------------------
# NEW bold family: simulated annealing over d-regular bipartite graphs with
# sides A = {0..N-1} and B = {N..2N-1}. Moves are double-edge swaps, which keep
# the graph d-regular and bipartite. The cost is the number of unordered pairs
# at distance greater than D. Zero cost means a valid graph of order 2N.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _sa_regular(N, d, D, rng, deadline, iters):
    """Try to find a d-regular bipartite graph on N+N vertices with diameter <= D."""
    n = 2 * N
    shifts = rng.sample(range(N), d)
    adj = [[] for _ in range(n)]
    for a in range(N):
        for s in shifts:
            b = N + (a + s) % N
            adj[a].append(b)
            adj[b].append(a)

    def apply(a1, b1, a2, b2):
        # Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1).
        adj[a1][adj[a1].index(b1)] = b2
        adj[a2][adj[a2].index(b2)] = b1
        adj[b1].remove(a1)
        adj[b1].append(a2)
        adj[b2].remove(a2)
        adj[b2].append(a1)

    def move():
        a1 = rng.randrange(N)
        b1 = adj[a1][rng.randrange(d)]
        a2 = rng.randrange(N)
        if a2 == a1:
            return None
        b2 = adj[a2][rng.randrange(d)]
        if b2 in adj[a1] or b1 in adj[a2]:
            return None
        apply(a1, b1, a2, b2)
        return (a1, b1, a2, b2)

    def undo(a1, b1, a2, b2):
        apply(a1, b2, a2, b1)

    for _ in range(10 * N):  # mix away from the circulant start
        move()

    cost = _bad(n, adj, D)
    T0, T1 = 1.5, 0.05
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        mv = move()
        if mv is None:
            continue
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            undo(*mv)

    if cost != 0:
        return None
    return [(a, b) for a in range(N) for b in adj[a]]


def _sa_phase(d, D, rng, deadline, cur):
    """Grow N one step at a time: each success gives a valid graph of order 2N."""
    N = cur[0][0] // 2 + 1
    while time.monotonic() < deadline:
        res = _sa_regular(N, d, D, rng, deadline, 3000)
        if res is not None:
            _consider(cur, 2 * N, res, d, D)
            N = max(N + 1, cur[0][0] // 2 + 1)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    cur = [lib.haar_graph(d, range(d))]

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            _consider(cur, pg[0], pg[1], d, D)

    if D >= 4 and d >= 3:
        # Short voltage-lift phase, then the annealed regular bipartite search.
        _voltage_phase(d, D, rng, start + 0.2 * time_limit, cur)
        _sa_phase(d, D, rng, start + 0.85 * time_limit, cur)

    best = cur[0]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
