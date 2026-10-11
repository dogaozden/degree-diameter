import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: projective plane for D = 3, cycle for d = 2, K_{d,d} as fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bitset bi-Cayley lifts over Z_G with k base vertices per side.
#
# Vertices: A_{i,x} = i*G + x and B_{j,y} = k*G + j*G + y.
# A dart (i, j, s) joins A_{i,x} to B_{j,x+s} for all x. Each A_i and each B_j
# gets exactly d darts (one per layer, layers use permutations), so the graph
# is d-regular. Translation by Z_G is an automorphism, so eccentricities only
# need to be checked from A_{i,0} and B_{j,0}.
#
# Reachable sets are Python big-int bitsets, and a rotation by s is a shift.
# This makes the annealing inner loop far cheaper than per-vertex BFS.
# ----------------------------------------------------------------------------

BIG_ITERS = 20000
T_END = 0.2


def _rot(X, s, G, mask):
    """Bitset of {x + s mod G : x in X}."""
    if s == 0:
        return X
    return ((X << s) | (X >> (G - s))) & mask


def _reach(k, G, D, Anb, Bnb, mask, side, b):
    """Number of vertices within distance D of the source (side, base b, offset 0)."""
    vis = [[0] * k, [0] * k]
    fr = [0] * k
    fr[b] = 1
    vis[side][b] = 1
    cnt = 1
    cur = side
    for _ in range(D):
        nxt = [0] * k
        if cur == 0:
            for i in range(k):
                f = fr[i]
                if f:
                    for j, s in Anb[i]:
                        nxt[j] |= _rot(f, s, G, mask)
            target = 1
        else:
            for j in range(k):
                f = fr[j]
                if f:
                    for i, s in Bnb[j]:
                        nxt[i] |= _rot(f, s, G, mask)
            target = 0
        any_new = False
        vt = vis[target]
        for t in range(k):
            x = nxt[t] & ~vt[t]
            if x:
                vt[t] |= x
                cnt += x.bit_count()
                any_new = True
            nxt[t] = x
        if not any_new:
            break
        fr = nxt
        cur = target
    return cnt


def _cost(k, G, D, darts, mask):
    """Unreached (source, vertex) pairs over all 2k sources, plus a duplicate-edge penalty."""
    Anb = [[] for _ in range(k)]
    Bnb = [[] for _ in range(k)]
    keys = set()
    for i, j, s in darts:
        Anb[i].append((j, s))
        Bnb[j].append((i, (G - s) % G))
        keys.add((i, j, s))
    dup = len(darts) - len(keys)
    total = 0
    full = 2 * k * G
    for side in (0, 1):
        for b in range(k):
            total += full - _reach(k, G, D, Anb, Bnb, mask, side, b)
    return total + 2 * G * dup


def _edges(k, G, darts):
    E = set()
    for i, j, s in darts:
        for x in range(G):
            E.add((i * G + x, k * G + j * G + (x + s) % G))
    return 2 * k * G, sorted(E)


def _anneal(k, d, G, D, rng, deadline, iters):
    """Simulated annealing over shifts and per-layer B-assignments; returns (n, edges) or None."""
    mask = (1 << G) - 1
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, mask)
    T0 = 1.0 + 0.05 * cost
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        frac = it / iters
        T = T0 * (1.0 - frac) + T_END
        if k == 1 or rng.random() < 0.7:
            e = rng.randrange(len(darts))
            old = darts[e][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[e][2] = new
            c2 = _cost(k, G, D, darts, mask)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[e][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ea, eb = L * k + a, L * k + b
            darts[ea][1], darts[eb][1] = darts[eb][1], darts[ea][1]
            c2 = _cost(k, G, D, darts, mask)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ea][1], darts[eb][1] = darts[eb][1], darts[ea][1]
    if cost != 0:
        return None
    return _edges(k, G, darts)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley lifts with 1..3 base vertices per side over Z_G,
    # aiming just above the current best order.
    ITERS = BIG_ITERS
    while best[0] < moore and time.monotonic() < deadline:
        k = rng.choice((1, 2, 3))
        lo = best[0] // (2 * k) + 1
        if 2 * k * lo > moore:
            break
        G = lo + rng.randrange(0, max(2, lo // 20))
        if 2 * k * G > moore or G < 2:
            continue
        res = _anneal(k, d, G, D, rng, deadline, ITERS)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
