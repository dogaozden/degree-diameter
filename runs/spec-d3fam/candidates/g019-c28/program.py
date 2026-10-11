import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Safe base constructions.
# ----------------------------------------------------------------------------

def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree q+2) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over groups of order G.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for all g. Left translations by
# the group preserve edges and act transitively on each layer, so the
# diameter check only needs BFS from one A-representative and one
# B-representative per base vertex.
# ----------------------------------------------------------------------------

def _abelian(a, b):
    """Z_a x Z_b, element (x, y) coded as x*b + y."""
    def mul(x, y):
        x1, y1 = divmod(x, b)
        x2, y2 = divmod(y, b)
        return ((x1 + x2) % a) * b + (y1 + y2) % b
    return a * b, mul


def _sample_group(G, rng):
    """Random group of order G: abelian Z_a x Z_b or a semidirect product Z_m x| Z_k2."""
    divs = [x for x in range(1, G + 1) if G % x == 0]
    if G < 2:
        return None
    if rng.random() < 0.5:
        b = rng.choice(divs)
        return _abelian(G // b, b)
    # Semidirect products with a random factorisation G = m * k2, k2 >= 2.
    cands = [k2 for k2 in divs if k2 >= 2 and (G // k2) >= 2]
    if not cands:
        return _abelian(G, 1)
    for _ in range(30):
        k2 = rng.choice(cands)
        m = G // k2
        r = rng.randrange(1, m) if m > 1 else 0
        if m > 1 and (math.gcd(r, m) != 1 or pow(r, k2, m) != 1 % m):
            continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r if m > 1 else 0)
        except ValueError:
            continue
        return order, mul
    return _abelian(G, 1)


def _perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Count (representative, vertex) pairs at distance > D. Zero means valid."""
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


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.3, T0 * (1.0 - it / iters))

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
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
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        rec = _araujo(d)
        if rec is not None:
            consider(rec[0], rec[1])

        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: annealed bi-Cayley lifts over abelian and semidirect groups,
    # with group orders chosen just above what the current best would need.
    ks = [1, 2, 2, 3, 3, 4] if D >= 3 else [1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        lo = best_n // (2 * k) + 1
        G = lo + rng.randrange(0, 6)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=300)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
