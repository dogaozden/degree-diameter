import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constructions:
#   D = 3: incidence graph of PG(2, q), q the largest prime power with q+1 <= d.
#   D >= 4: multi-base voltage lifts (k base vertices per side) over a group G
#           of order G, giving a graph on 2kG vertices. Groups are cyclic,
#           direct products Z_a x Z_b, or semidirect products Z_m x| Z_k.
#           Voltages are found by simulated annealing on the number of
#           (representative, vertex) pairs at distance > D. Left translation
#           is an automorphism, so the block representatives suffice.
# Every candidate is checked with lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
ANNEAL_ITERS = 1200   # annealing steps per attempt
BAND = 8              # order window above the current lower bound
_TABLES = {}


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _table(G, mul):
    """cols[g][x] = x * g, the right-multiplication permutation for each g."""
    return [[mul(x, g) for x in range(G)] for g in range(G)]


def _dp(a, b):
    """Multiplication on Z_a x Z_b, element x coded as i*b + j."""
    def mul(x, y):
        i1, j1 = divmod(x, b)
        i2, j2 = divmod(y, b)
        return ((i1 + i2) % a) * b + (j1 + j2) % b
    return mul


def _groups(G):
    """List of right-multiplication tables for several groups of order G (cached)."""
    hit = _TABLES.get(G)
    if hit is not None:
        return hit
    out = [_table(G, lambda x, y: (x + y) % G)]
    for a in range(2, G):
        if G % a == 0 and G // a >= 2 and a <= G // a:
            out.append(_table(G, _dp(a, G // a)))
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                order, mul, _ = lib.semidirect_group(m, k, r)
                out.append(_table(order, mul))
                break
    if len(_TABLES) >= 64:
        _TABLES.clear()
    _TABLES[G] = out
    return out


def _cost(k, G, D, darts, cols):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
    if len({(i, j, g) for i, j, g in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, g in darts:
        col = cols[g]
        ba = i * G
        bb = (k + j) * G
        for x in range(G):
            a = ba + x
            b = bb + col[x]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, cols):
    E = set()
    for i, j, g in darts:
        col = cols[g]
        for x in range(G):
            E.add((i * G + x, (k + j) * G + col[x]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, cols, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, cols)
    T0, T1 = 1.5, 0.2
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (T1 / T0) ** (it / max(1, iters))
        if rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, cols)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, cols)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, darts, cols)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return lib.haar_graph(d, range(d))

    # D >= 4: multi-base voltage lift search aimed above the current best.
    ks = (2, 3)
    tries = 0
    exceeded = set()
    try:
        while best[0] < moore and time.monotonic() < deadline:
            k = ks[tries % 2]
            tries += 1
            lo = best[0] // (2 * k) + 1
            if 2 * k * lo > moore:
                exceeded.add(k)
                if len(exceeded) == len(ks):
                    break
                continue
            if rng.random() < 0.5:
                G = lo
            else:
                G = lo + rng.randrange(BAND)
            if 2 * k * G > moore:
                G = lo
            if G < 3:
                continue
            groups = _groups(G)
            cols = rng.choice(groups)
            res = _anneal(d, D, k, G, cols, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
