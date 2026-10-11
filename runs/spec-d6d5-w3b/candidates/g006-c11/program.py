import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallback and D = 3 families.
# ----------------------------------------------------------------------------

def _fallback(d):
    """K_{d,d}: bipartite, degree d, diameter 2 (valid for every D >= 2)."""
    return lib.haar_graph(d, range(d))


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Different construction for D >= 4: bi-Cayley lifts over semidirect products
# Z_m x| Z_k2, with the wiring annealed against a bit-parallel distance cost.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h, with G = |group|.
# Each of the d "layers" is a perfect matching between the k A-blocks and the
# k B-blocks; every dart (i, j, s) joins A_i,g to B_j, g*s for all g.
# Left multiplication by a group element is an automorphism, so the distance
# condition only has to be checked from the 2k block identities.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    for _ in range(60):
        k2 = rng.choice([1, 2, 3, 4, 5, 6, 8])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
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


def _cost(k, G, D, darts, mul):
    """Sum over the 2k block identities of the number of vertices farther than D. Zero means valid."""
    N = 2 * k * G
    S = 2 * k
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + mul(g, s)
            adj[a].append(b)
            adj[b].append(a)
    # Bit t of R[v] is set iff source t is within the current radius of v.
    R = [0] * N
    for t in range(k):
        R[t * G] |= 1 << t
        R[(k + t) * G] |= 1 << (k + t)
    for _ in range(D):
        newR = []
        for v in range(N):
            x = R[v]
            for u in adj[v]:
                x |= R[u]
            newR.append(x)
        R = newR
    total = sum(x.bit_count() for x in R)
    return S * N - total


def _lift_edges(k, G, darts, mul):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + mul(g, s)))
    return sorted(E)


def _anneal(k, G, d, D, mul, rng, deadline, iters):
    """Anneal voltages and layer matchings. Returns (darts, cost)."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, mul)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(G)
            c2 = _cost(k, G, D, darts, mul)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, mul)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, cost


def _saturate(n, edges, d, color, rng):
    """Add edges between deficient opposite-colour vertices (keeps bipartiteness, degree, diameter)."""
    E = list(edges)
    deg = [0] * n
    ex = set()
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
        ex.add((min(u, v), max(u, v)))
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in ex]
    rng.shuffle(pairs)
    for a, b in pairs:
        key = (min(a, b), max(a, b))
        if deg[a] < d and deg[b] < d and key not in ex:
            E.append((a, b))
            ex.add(key)
            deg[a] += 1
            deg[b] += 1
    return E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.80 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo_candidate(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4:
        while time.monotonic() < deadline:
            k = rng.choice([1, 2, 2, 3, 4])
            lo = max(2, best_n // (2 * k) + 1)
            hi = lo + max(3, lo // 5)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            iters = 400 if k == 1 else 250
            darts, c = _anneal(k, order, d, D, mul, rng, deadline, iters)
            if c != 0:
                continue
            n = 2 * k * order
            E = _lift_edges(k, order, darts, mul)
            color = [0] * (k * order) + [1] * (k * order)
            E = _saturate(n, E, d, color, rng)
            consider(n, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d)
    return best
