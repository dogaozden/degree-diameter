import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Diameter-3 bases: projective plane and the Araujo-Pardo / Lopez record family.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    """Record family of degree d = q + 2 when q = d - 2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g  and  B_{j,h} = (k+j)*G + h.
# A dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every group element g.
# Left multiplication by a group element is an automorphism of the lift, so
# the diameter check only needs BFS-style balls from one representative per
# layer. Balls are kept as Python big-int bitmasks, which makes each cost
# evaluation a few milliseconds.
#
# Each layer is a perfect matching between the k A-vertices and the k
# B-vertices, so every vertex has degree exactly d and no pair of darts
# can create a duplicate edge.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G; returns (order, mul) or None."""
    opts = [k2 for k2 in (1, 2, 3, 4, 5, 6, 8, 10, 12)
            if G % k2 == 0 and G // k2 >= 2]
    if not opts:
        return None
    k2 = rng.choice(opts)
    m = G // k2
    if k2 == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mul, _ = lib.semidirect_group(m, k2, r)
    except ValueError:
        return None
    return order, mul


def _ball_cost(N, adj, D, reps):
    """Total number of vertices missed within distance D, summed over the representatives."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        if new == reach:
            break
        reach = new
    return sum(N - reach[r].bit_count() for r in reps)


def _cost(k, G, D, darts, table):
    """Zero exactly when the bi-Cayley lift has diameter <= D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + table[g][s]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    return _ball_cost(N, adj, D, reps)


def _to_edges(k, G, darts, table):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + table[g][s]
            E.add((min(a, b), max(a, b)))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, table, rng, deadline, iters):
    """Simulated annealing over dart shifts and per-layer target permutations."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, table)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 2.0 * (0.05) ** (it / max(1, iters))
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, table)
            if c2 <= cost or rng.random() < math.exp(-min(50.0, (c2 - cost) / T)):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, table)
            if c2 <= cost or rng.random() < math.exp(-min(50.0, (c2 - cost) / T)):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return darts
    return None


def _bicayley_search(d, D, best, rng, deadline, state):
    """Repeatedly look for a valid lift strictly larger than the current best."""
    while time.monotonic() < deadline:
        best_n = state['best'][0]
        k = rng.choice([1, 2, 2, 3, 3, 4, 5])
        G = best_n // (2 * k) + 1 + rng.randrange(0, 3)
        if G < 2:
            continue
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        table = [[mul(x, s) for s in range(order)] for x in range(order)]
        darts = _anneal(d, D, k, order, table, rng, deadline, iters=1200)
        if darts is not None:
            n, e = _to_edges(k, order, darts, table)
            if n > state['best'][0] and lib.is_valid(n, e, d, D):
                state['best'] = (n, e)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _build_inner(d, D, seed, time_limit, start, state):
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    def consider(n, e):
        if n > state['best'][0] and lib.is_valid(n, e, d, D):
            state['best'] = (n, e)

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo_candidate(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4:
        _bicayley_search(d, D, state['best'], rng, deadline, state)


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    state = {'best': fallback}

    try:
        _build_inner(d, D, seed, time_limit, start, state)
    except Exception:
        pass  # keep the best valid graph found so far

    best = state['best']
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
