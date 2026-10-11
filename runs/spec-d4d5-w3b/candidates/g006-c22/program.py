import math
import random
import time

import lib


BIG = 10 ** 6


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    opts = [k2 for k2 in (1, 2, 3, 4, 5, 6, 8, 9, 10, 12) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(opts)
    for k2 in opts:
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(d, k, G, D, perm, volt, R):
    """Number of (representative, vertex) pairs not within distance D; BIG if darts repeat."""
    seen_darts = set()
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for L in range(d):
        for i in range(k):
            j = perm[L][i]
            s = volt[L][i]
            key = (i, j, s)
            if key in seen_darts:
                return BIG
            seen_darts.add(key)
            pm = R[s]
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
    return total


def _edges(d, k, G, perm, volt, R):
    E = set()
    for L in range(d):
        for i in range(k):
            j = perm[L][i]
            pm = R[volt[L][i]]
            for g in range(G):
                E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, R, rng, deadline):
    """Anneal voltages and per-layer B-assignments; a layer is a permutation so degrees stay d."""
    perm = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    cost = _cost(d, k, G, D, perm, volt, R)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    T0, T1 = 3.0, 0.3
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t_start) / span)
        if k < 2 or rng.random() < 0.6:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volt[L][i] = new
            c2 = _cost(d, k, G, D, perm, volt, R)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                volt[L][i] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            perm[L][a], perm[L][b] = perm[L][b], perm[L][a]
            c2 = _cost(d, k, G, D, perm, volt, R)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                perm[L][a], perm[L][b] = perm[L][b], perm[L][a]
    if cost == 0:
        return _edges(d, k, G, perm, volt, R)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Baseline: projective plane incidence graph (diameter 3) when d-1 is a prime power.
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        consider(n0, e0)

    # Main search: bi-Cayley voltage lifts over semidirect products, annealed.
    ks = [1, 2, 2, 3, 3, 4, 5, 6] if D >= 5 else [1, 2, 3]
    while time.monotonic() < end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        R = [[mul(x, s) for x in range(order)] for s in range(order)]
        now = time.monotonic()
        slice_end = min(end, now + max(1.0, 0.25 * (end - now)))
        res = _anneal(d, D, k, order, R, rng, slice_end)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
