import math
import random
import time

import lib

# Bold change for the weak target (d=4, D=5): the parent's search is replaced by
# annealed bi-Cayley lifts over semidirect products with a bitset-parallel
# diameter cost, base sizes up to k=4 per side, and a target that always sits
# just above the current best order. Everything else falls back to the
# projective-plane or K_{d,d} constructions, and every returned graph is
# checked by lib.is_valid.


def _cost_bits(N, adj, D):
    """Total number of (source, target) pairs not within distance D, computed with bitsets."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(N - b.bit_count() for b in ball)


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


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages and per-layer B-targets of a bi-Cayley lift until diameter <= D."""
    N = 2 * k * G
    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    # darts: [i, j, s]; each layer L contributes one dart per A-index i, with
    # j a permutation of range(k), so every vertex has degree exactly d.
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    def cost_of(ds):
        adj = [[] for _ in range(N)]
        for i, j, s in ds:
            pm = perm(s)
            for g in range(G):
                a = i * G + g
                b = (k + j) * G + pm[g]
                adj[a].append(b)
                adj[b].append(a)
        return _cost_bits(N, adj, D)

    c = cost_of(darts)
    T0 = max(1.0, 0.05 * c)
    T_end = 0.3
    for it in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T_end / T0) ** (it / max(1, iters))
        cand = [row[:] for row in darts]
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(cand))
            new_s = rng.randrange(G)
            if new_s == cand[idx][2]:
                continue
            cand[idx][2] = new_s
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            cand[ia][1], cand[ib][1] = cand[ib][1], cand[ia][1]
        c2 = cost_of(cand)
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            darts = cand
            c = c2

    if c != 0:
        return None
    E = set()
    for i, j, s in darts:
        pm = perm(s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return N, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective-plane base for D >= 3 (diameter 3 when d-1 is a prime power).
    if D >= 3 and d >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break

    # Annealed bi-Cayley lift search, aimed just above the current best order.
    if D >= 4 and d >= 2:
        ks = [1, 1, 2, 2, 3, 4]
        iters = 1500 if D >= 5 else 600
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            target = best_n + 2
            G = max(2, -(-target // (2 * k)) + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
