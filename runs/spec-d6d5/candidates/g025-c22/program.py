import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks: K_{d,d} (diameter 2) and the projective-plane incidence graph.
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over Z_m with k base vertices per side.
#
# Base: d perfect matchings between A_0..A_{k-1} and B_0..B_{k-1} (layer l
# matches A_i to B_{perms[l][i]}), each dart carrying a voltage in Z_m.
# Lift: A_{i,g} = i*m + g,  B_{j,h} = (k+j)*m + h,
#       dart (l, i) joins A_{i,g} to B_{perms[l][i], g + volt[l][i]} for all g.
# Each lift vertex has degree d (before duplicate removal).
#
# Diameter is checked by a bit-parallel BFS: reach[v] is an N-bit integer
# with bit w set when w is within distance t of v. The lift is vertex-transitive
# within each side, so it suffices to look at the k A-representatives and the
# k B-representatives.
# ----------------------------------------------------------------------------

def _cost(k, m, d, perms, volt, D):
    """Number of (representative, vertex) pairs at distance > D. Zero iff the lift has diameter <= D."""
    N = 2 * k * m
    adj = [[] for _ in range(N)]
    for l in range(d):
        p, vl = perms[l], volt[l]
        for i in range(k):
            j, s = p[i], vl[i]
            ba, bb = i * m, (k + j) * m
            for g in range(m):
                a = ba + g
                b = bb + (g + s) % m
                adj[a].append(b)
                adj[b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = [0] * N
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            nxt[v] = x
        reach = nxt
    total = 0
    reps = list(range(0, k * m, m)) + list(range(k * m, N, m))
    for r in reps:
        total += N - reach[r].bit_count()
    return total


def _lift(k, m, d, perms, volt):
    """Edges of the lift; A-side vertices are 0..k*m-1 and B-side are k*m..2*k*m-1."""
    E = set()
    for l in range(d):
        p, vl = perms[l], volt[l]
        for i in range(k):
            j, s = p[i], vl[i]
            for g in range(m):
                E.add((i * m + g, (k + j) * m + (g + s) % m))
    return 2 * k * m, sorted(E)


def _anneal(k, m, d, D, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-targets. Returns (cost, perms, volt)."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
    cost = _cost(k, m, d, perms, volt, D)
    T = 3.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.2, T * 0.999)
        if k == 1 or rng.random() < 0.6:
            # Voltage move.
            l, i = rng.randrange(d), rng.randrange(k)
            old = volt[l][i]
            new = rng.randrange(m)
            if new == old:
                continue
            volt[l][i] = new
            c2 = _cost(k, m, d, perms, volt, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                volt[l][i] = old
        else:
            # Target move: swap the B-targets of two A-vertices in one layer
            # (keeps each layer a perfect matching, so the lift stays d-regular).
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            p = perms[l]
            p[i1], p[i2] = p[i2], p[i1]
            c2 = _cost(k, m, d, perms, volt, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                p[i1], p[i2] = p[i2], p[i1]
    return cost, perms, volt


def _saturate(half, n, edges, d, rng):
    """Add edges between deficient opposite-side vertices. Only adds edges, so the diameter cannot grow."""
    E = set(edges)
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    A = [a for a in range(half) if deg[a] < d]
    B = [b for b in range(half, n) if deg[b] < d]
    pairs = [(a, b) for a in A for b in B if (a, b) not in E]
    rng.shuffle(pairs)
    out = list(E)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe baseline: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D <= 3:
        return best_n, best_e

    # Main search: annealed bi-Cayley lifts over Z_m with k base vertices per side.
    # Each success raises the target, so the search ratchets upward.
    ks = [1, 1, 2, 2, 3, 4]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        lo = best_n // (2 * k) + 1
        m = max(2, lo + rng.randrange(0, 3))
        cost, perms, volt = _anneal(k, m, d, D, rng, deadline, 1500)
        if cost != 0:
            continue
        n, e = _lift(k, m, d, perms, volt)
        n, e = _saturate(k * m, n, e, d, rng)
        consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
