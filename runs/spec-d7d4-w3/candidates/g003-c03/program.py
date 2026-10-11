import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
#   D = 3: incidence graph of PG(2, q), q + 1 <= d (meets Moore bound when d-1 = q).
#   D >= 4: incidence graph of the generalized quadrangle W(q), degree q + 1, diameter 4.
# These are the safe starting points and the fallback floor.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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


# ----------------------------------------------------------------------------
# High-risk construction: bi-Cayley voltage lifts over a group G (cyclic or
# semidirect Z_m x| Z_k2), with k base vertices per side and d "layers".
#
# Layer L is a permutation p_L of range(k) plus voltages s_{L,i} in G.
# Left fiber i and right fiber j are copies of G; for each layer L the edges
#     (i, x) -- (p_L(i), x * s_{L,i})
# are added for every x in G. Every vertex then has degree exactly d, the
# graph is bipartite by construction, and G acts regularly on each fiber by
# left multiplication. So the diameter only needs checking from the 2k fiber
# representatives (i, e) to every vertex.
#
# Search: simulated annealing over permutations and voltages, minimising the
# number of (representative, vertex) pairs at distance > D. Zero means valid.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (G, mul_table) for a group of order G (semidirect product if possible, else cyclic)."""
    if rng.random() < 0.6:
        ks = [k2 for k2 in (2, 3, 4) if G % k2 == 0 and G // k2 >= 3]
        if ks:
            k2 = rng.choice(ks)
            m = G // k2
            cands = [r for r in range(2, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
                _, mul, _ = lib.semidirect_group(m, k2, r)
                return G, [[mul(x, y) for y in range(G)] for x in range(G)]
    return G, [[(x + y) % G for y in range(G)] for x in range(G)]


def _lift_cost(k, G, d, D, T, perm, volt, limit):
    """Number of (representative, vertex) pairs at distance > D; 0 means valid."""
    keys = set()
    dup = 0
    for L in range(d):
        pl = perm[L]
        vl = volt[L]
        for i in range(k):
            key = (i, pl[i], vl[i])
            if key in keys:
                dup += 1
            else:
                keys.add(key)
    if dup:
        return 1000000 + dup

    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for L in range(d):
        pl = perm[L]
        vl = volt[L]
        for i in range(k):
            j = pl[i]
            s = vl[i]
            base_a = i * G
            base_b = (k + j) * G
            for x in range(G):
                a = base_a + x
                b = base_b + T[x][s]
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
        if total > limit:
            return total
    return total


def _lift_edges(k, G, d, T, perm, volt):
    E = []
    for L in range(d):
        for i in range(k):
            j = perm[L][i]
            s = volt[L][i]
            for x in range(G):
                E.append((i * G + x, (k + j) * G + T[x][s]))
    return 2 * k * G, E


def _anneal(k, G, d, D, T, rng, deadline):
    """Anneal voltages and layer permutations until the lift has diameter <= D. Returns (n, edges) or None."""
    perm = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    cost = _lift_cost(k, G, d, D, T, perm, volt, float("inf"))
    start = time.monotonic()
    span = max(1e-3, deadline - start)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        temp = 1.5 * (0.02 ** ((now - start) / span))
        limit = cost - temp * math.log(1.0 - rng.random())

        if k == 1 or rng.random() < 0.6:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volt[L][i] = new
            c2 = _lift_cost(k, G, d, D, T, perm, volt, limit)
            if c2 <= limit:
                cost = c2
            else:
                volt[L][i] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            pl = perm[L]
            pl[a], pl[b] = pl[b], pl[a]
            c2 = _lift_cost(k, G, d, D, T, perm, volt, limit)
            if c2 <= limit:
                cost = c2
            else:
                pl[a], pl[b] = pl[b], pl[a]

    return _lift_edges(k, G, d, T, perm, volt)


def _lift_search(d, D, holder, rng, deadline, slot):
    """Repeatedly try to beat holder[0] with fresh lifts of a random size and group."""
    while time.monotonic() < deadline - 0.2:
        best_n = holder[0][0]
        k = rng.choice([1, 2, 2, 3, 3, 4])
        target = best_n + 1 + rng.randrange(0, 4)
        G = max(2, -(-target // (2 * k)) + rng.randrange(0, 2))
        order, T = _sample_group(G, rng)
        end = min(deadline, time.monotonic() + slot)
        res = _anneal(k, order, d, D, T, rng, end)
        if res is not None:
            n, e = res
            if n > holder[0][0] and lib.is_valid(n, e, d, D):
                holder[0] = (n, e)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Algebraic base graphs.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break
    elif D >= 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                n, e = _gq_w(q)
                consider(n, e)
                break

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Bold search: bi-Cayley voltage lifts, annealed, aiming above the current best.
    holder = [best]
    slot = max(1.5, 0.08 * time_limit)
    _lift_search(d, D, holder, rng, deadline, slot)
    if holder[0][0] > best[0]:
        consider(holder[0][0], holder[0][1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
