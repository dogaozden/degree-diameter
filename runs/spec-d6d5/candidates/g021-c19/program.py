import math
import random
import time

import lib

_BIG = 10 ** 9


def _pick_group(order, rng):
    """Multiplication of a random semidirect product Z_a x| Z_b with a*b = order (identity coded as 0), or None."""
    divs = [b for b in range(1, order + 1) if order % b == 0]
    for _ in range(40):
        b = rng.choice(divs)
        a = order // b
        if b == 1:
            r = 1 % a
        else:
            cands = [r for r in range(1, a)
                     if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            _, mul, _ = lib.semidirect_group(a, b, r)
        except ValueError:
            continue
        return mul
    return None


def _score(bn, G, bdarts, volt, perms, D):
    """Unreached (representative, vertex) pairs within distance D of the lift. Zero means valid.

    Left multiplication acts regularly on each fibre, so the representatives (u, identity) suffice.
    """
    keys = set()
    for (u, v), g in zip(bdarts, volt):
        keys.add((u, v, g))
    if len(keys) < len(bdarts):
        return _BIG
    N = bn * G
    adj = [[] for _ in range(N)]
    for (u, v), pm in zip(bdarts, perms):
        ub, vb = u * G, v * G
        for x in range(G):
            a = ub + x
            b = vb + pm[x]
            adj[a].append(b)
            adj[b].append(a)
    ball = [1 << i for i in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = ball[v]
            for w in adj[v]:
                x |= ball[w]
            new[v] = x
        ball = new
    total = 0
    for u in range(bn):
        total += N - ball[u * G].bit_count()
    return total


def _anneal(bn, G, bdarts, mul, D, rng, deadline, iters):
    """Simulated annealing over the voltages of a base multigraph. Returns (success, volt, perms)."""
    E = len(bdarts)
    volt = [rng.randrange(G) for _ in range(E)]
    perms = [[mul(x, g) for x in range(G)] for g in volt]
    cur = _score(bn, G, bdarts, volt, perms, D)
    T0 = 2.0
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - it / iters) + 0.05
        e = rng.randrange(E)
        old = volt[e]
        new = rng.randrange(G)
        if new == old:
            continue
        old_perm = perms[e]
        volt[e] = new
        perms[e] = [mul(x, new) for x in range(G)]
        c = _score(bn, G, bdarts, volt, perms, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            volt[e] = old
            perms[e] = old_perm
    return cur == 0, volt, perms


def _lift_edges(bn, G, bdarts, perms):
    edges = []
    for (u, v), pm in zip(bdarts, perms):
        for x in range(G):
            edges.append((u * G + x, v * G + pm[x]))
    return bn * G, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    kd = lib.haar_graph(d, range(d))
    best = kd

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D <= 2:
        return best

    # Bases: projective plane incidence (degree d, diameter 3) when d-1 is a prime power,
    # and the two-vertex base with d parallel darts (bi-Cayley / Haar lifts).
    bases = []
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        n2, pe = lib.projective_plane_incidence(q)
        consider(n2, pe)
        bases.append((n2 // 2 * 0 + n2, [(u, v) for u, v in pe]))
        # bn for the PG base is n2 (all vertices are base vertices)
    bases.append((2, [(0, 1)] * d))

    rng = random.Random(seed * 1000003 + d * 101 + D)
    while time.monotonic() < deadline:
        bn, bdarts = rng.choice(bases) if len(bases) == 1 else (
            bases[0] if rng.random() < 0.6 else bases[-1])
        need = (best[0] + 1 + bn - 1) // bn
        G = need + rng.choice([0, 0, 1])
        if G < 2:
            G = 2
        mul = _pick_group(G, rng)
        if mul is None:
            continue
        slice_end = min(deadline, time.monotonic() + 10.0)
        ok, volt, perms = _anneal(bn, G, bdarts, mul, D, rng, slice_end, 4000)
        if ok:
            n, e = _lift_edges(bn, G, bdarts, perms)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = kd
    return best
