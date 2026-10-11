import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cheap algebraic bases (projective plane, Araujo-Pardo & Lopez for D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, searched by annealing.
#
# Base graph: k vertices on each side, d "layers". Layer L is a permutation p_L
# of range(k) plus one voltage v_{L,i} per i. The dart (L, i) joins
#   A_{i,g} = i*G + g    to    B_{p_L(i), g*v} = (k + p_L(i))*G + mul(g, v).
# Every A and every B vertex then has degree exactly d (one edge per layer).
#
# Cost is the number of (vertex, vertex) pairs at distance > D, computed with
# bitmask reachability over the whole lift, plus a penalty for repeated darts
# (which would create multi-edges). Cost 0 means valid.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a semidirect product Z_m x| Z_k2 of order G."""
    divs = [k2 for k2 in range(1, min(G, 12) + 1) if G % k2 == 0 and G // k2 >= 2]
    k2 = rng.choice(divs) if divs else 1
    m = G // k2
    if k2 > 1:
        cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            r = rng.choice(cands)
            order, mul, _ = lib.semidirect_group(m, k2, r)
            return order, mul
    order, mul, _ = lib.semidirect_group(G, 1, 1)
    return order, mul


def _cost(k, G, D, layers, tab):
    """Unreached (vertex, vertex) pairs at distance > D, plus a penalty for duplicate darts."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    seen = set()
    dup = 0
    for p, v in layers:
        for i in range(k):
            key = (i, p[i], v[i])
            if key in seen:
                dup += 1
            else:
                seen.add(key)
            j, s = p[i], v[i]
            row = tab[s]
            base_a = i * G
            base_b = (k + j) * G
            for g in range(G):
                a = base_a + g
                b = base_b + row[g]
                adj[a].append(b)
                adj[b].append(a)
    reach = [1 << x for x in range(N)]
    for _ in range(D):
        new = []
        for x in range(N):
            r = reach[x]
            for y in adj[x]:
                r |= reach[y]
            new.append(r)
        reach = new
    unreached = sum(N - r.bit_count() for r in reach)
    return dup * N + unreached


def _edges_from(k, G, layers, tab):
    E = []
    for p, v in layers:
        for i in range(k):
            j, s = p[i], v[i]
            row = tab[s]
            for g in range(G):
                E.append((i * G + g, (k + j) * G + row[g]))
    return 2 * k * G, E


def _anneal(d, D, k, G, tab, rng, deadline, max_iters):
    """Simulated annealing over voltages and per-layer B-assignments. Returns layers or None."""
    layers = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        v = [rng.randrange(G) for _ in range(k)]
        layers.append([p, v])
    c = _cost(k, G, D, layers, tab)
    T = 1.0
    for _ in range(max_iters):
        if c == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.998)
        L = rng.randrange(d)
        p, v = layers[L]
        if k == 1 or rng.random() < 0.7:
            i = rng.randrange(k)
            old = v[i]
            new = rng.randrange(G)
            if new == old:
                continue
            v[i] = new
            c2 = _cost(k, G, D, layers, tab)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                c = c2
            else:
                v[i] = old
        else:
            i, j = rng.sample(range(k), 2)
            p[i], p[j] = p[j], p[i]
            c2 = _cost(k, G, D, layers, tab)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                c = c2
            else:
                p[i], p[j] = p[j], p[i]
    if c == 0:
        return layers
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2, valid for every D >= 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        # Araujo-Pardo & Lopez record family: d = q + 2, d - 1 not a prime power.
        q = d - 2
        if q >= 3 and lib.is_prime_power(q) and not lib.is_prime_power(d - 1):
            try:
                n_a, e_a = lib.araujo_lopez_graph(q)
                consider(n_a, e_a)
            except ValueError:
                pass

    # Main search: annealed bi-Cayley lifts over semidirect products, aiming above best_n.
    ks = [1, 2, 2, 3] if D >= 4 else [1, 1, 2]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(2, base // 10 + 1)))
        order, mul = _sample_group(G, rng)
        tab = [[mul(g, s) for g in range(order)] for s in range(order)]
        per_call_deadline = min(deadline, time.monotonic() + 8.0)
        layers = _anneal(d, D, k, order, tab, rng, per_call_deadline, max_iters=4000)
        if layers is not None:
            n, e = _edges_from(k, order, layers, tab)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
