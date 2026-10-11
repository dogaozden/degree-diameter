import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over Z_m x| Z_k2 with irregular base layers.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, for i, j in 0..k-1.
# A dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every group element g.
# Each A-layer carries exactly d darts, and each B-layer receives exactly d darts,
# so the lift is d-regular. Left multiplication is an automorphism, so only one
# representative per layer is needed when measuring distances.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    for _ in range(60):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(80):
                c = rng.randrange(1, m)
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(k, G, D, darts, pms):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
    seen = set()
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            return _BIG
        seen.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for idx, (i, j, _s) in enumerate(darts):
        pm = pms[idx]
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        mark = bytearray(N)
        mark[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not mark[v]:
                        mark[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, pms):
    E = set()
    for idx, (i, j, _s) in enumerate(darts):
        pm = pms[idx]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over dart voltages and B-layer assignments."""
    nd = d * k
    darts = [[t // d, t % k, rng.randrange(G)] for t in range(nd)]
    pms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, pms)
    T0, T1 = 2.0, 0.1

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))

        if rng.random() < 0.6 or k == 1:
            t = rng.randrange(nd)
            old = darts[t][2]
            new = rng.randrange(G)
            if new == old:
                continue
            oldpm = pms[t]
            darts[t][2] = new
            pms[t] = [mul(g, new) for g in range(G)]
            c2 = _cost(k, G, D, darts, pms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[t][2] = old
                pms[t] = oldpm
        else:
            a, b = rng.sample(range(nd), 2)
            if darts[a][1] == darts[b][1]:
                continue
            darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
            c2 = _cost(k, G, D, darts, pms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[a][1], darts[b][1] = darts[b][1], darts[a][1]

    if cost == 0:
        return _edges(k, G, darts, pms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.75 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D >= 3 and lib.is_prime_power(d - 1):
            # Projective plane incidence graph meets the Moore bound for D = 3.
            consider(*lib.projective_plane_incidence(d - 1))

        if D >= 3 and d >= 3:
            while time.monotonic() < deadline:
                k = rng.choice([1, 2, 2, 3, 4])
                target = best_n // (2 * k) + 1
                G = target + rng.randrange(0, 3)
                if G < 2:
                    continue
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _anneal(d, D, k, order, mul, rng, deadline, iters=1500)
                if res is not None:
                    consider(res[0], res[1])
    except Exception:
        pass

    try:
        valid = lib.is_valid(best[0], best[1], d, D)
    except Exception:
        valid = False
    if not valid:
        best = lib.haar_graph(d, range(d))
    return best
