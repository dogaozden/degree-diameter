import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 9


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6])
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
    """Anneal a bi-Cayley voltage lift over a group of order G with k base vertices per side.

    Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h. Each layer L contributes a
    perfect matching i -> j (a permutation) with a voltage s, joining A_{i,g} to B_{j,g*s}.
    Left multiplication is an automorphism, so BFS from one representative per side
    and layer suffices. Returns (n, edges) with diameter <= D, or None.
    """
    N = 2 * k * G
    ar = np.arange(G)
    reps = np.array([i * G for i in range(k)] + [(k + j) * G for j in range(k)], dtype=np.int64)
    ridx = np.arange(2 * k)

    def perm(s):
        return np.array([mul(g, s) for g in range(G)], dtype=np.int64)

    def cost(darts, perms):
        if len({(a, b, c) for a, b, c in darts}) < len(darts):
            return _BIG
        A = np.zeros((N, N), dtype=np.float32)
        for (i, j, _s), pm in zip(darts, perms):
            a = i * G + ar
            b = (k + j) * G + pm
            A[a, b] = 1.0
            A[b, a] = 1.0
        R = np.zeros((2 * k, N), dtype=np.float32)
        R[ridx, reps] = 1.0
        for _ in range(D):
            R = np.minimum(R + R @ A, 1.0)
        return int(round(2 * k * N - float(R.sum())))

    darts = None
    for _ in range(200):
        cand = []
        for _ in range(d):
            p = rng.sample(range(k), k)
            for i in range(k):
                cand.append([i, p[i], rng.randrange(G)])
        if len({tuple(x) for x in cand}) == len(cand):
            darts = cand
            break
    if darts is None:
        return None

    perms = [perm(s) for _, _, s in darts]
    cur = cost(darts, perms)
    T0 = max(1.0, 0.05 * cur)
    T_end = 0.3
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for it in range(iters):
        if cur == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            oldp = perms[idx]
            darts[idx][2] = new
            perms[idx] = perm(new)
            c2 = cost(darts, perms)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                darts[idx][2] = old
                perms[idx] = oldp
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = cost(darts, perms)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cur != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + int(pm[g])))
    return N, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
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

    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best

    # Known structured bases for D = 3.
    if D >= 3:
        try:
            pg = _pg_candidate(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
        try:
            q = d - 2
            if q >= 3 and lib.is_prime_power(q):
                n, e = lib.araujo_lopez_graph(q)
                consider(n, e)
        except Exception:
            pass

    # Main search: annealed bi-Cayley lifts over semidirect products, using a
    # numpy-based distance check. Group orders are chosen so that each accepted
    # lift strictly beats the current best order.
    if D >= 5:
        ks = [1, 1, 2, 2, 3, 4]
        iters = 6000
    else:
        ks = [1, 2, 3]
        iters = 2000

    try:
        while time.monotonic() < deadline and best_n < moore:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    try:
        ok = lib.is_valid(best[0], best[1], d, D)
    except Exception:
        ok = False
    if not ok:
        best = lib.haar_graph(d, range(d))
    return best
