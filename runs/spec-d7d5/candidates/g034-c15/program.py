import math
import random
import time

import numpy as np

import lib

# Bi-Cayley ladder search.
#
# Core idea: vertices are A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, where G is a
# finite group of order m*k2 (semidirect Z_m x| Z_k2, or a direct product when r = 1).
# Layer l joins A_i to B_{pi_l(i)} with voltage s: A_{i,g} ~ B_{pi_l(i), g*s}. Each
# layer is a perfect matching between the two sides, so every vertex has degree d.
#
# Unlike a target-driven search, this ladder asks for vertex counts just above the
# current best and lets the best grow one step at a time. Group orders are drawn from
# a broader family than before (direct products as well as semidirect products), and
# base sizes k in {1,2,3,4} are mixed. Every candidate is checked with lib.is_valid
# before it can replace the current best. The fallback is always a valid graph.

_PEN = 40
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _divisors(n):
    return [x for x in range(1, n + 1) if n % x == 0]


def _sample_group(order, rng):
    """Return (m, k2, r) with m * k2 == order. Semidirect Z_m x| Z_k2; r = 1 is the direct product."""
    divs = [x for x in _divisors(order) if x <= 60]
    k2 = rng.choice(divs)
    m = order // k2
    if k2 == 1 or rng.random() < 0.3:
        return m, k2, 1
    for _ in range(80):
        r = rng.randrange(2, m) if m > 2 else 1
        if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
            return m, k2, r
    return m, k2, 1


def _group_tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = h*s^{-1} (as element indices)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    # (a_g, b_g) * (a_s, b_s) = (a_g + r^{b_g} a_s, b_g + b_s)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))  # Invs[s, g*s] = g
    return G, Ts, Invs


def _anneal(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over layer permutations and voltages. Returns (n, edges) or None."""
    N = 2 * k * G
    nb = 2 * k
    pi = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def set_dart(l, i):
        j = pi[l][i]
        s = S[l][i]
        nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
        nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]

    def dups():
        keys = [(i, pi[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    def evaluate():
        # Bit b of reach[v] is set when v is within distance D of the root of block b.
        reach = np.zeros(N, dtype=np.int64)
        for b in range(nb):
            reach[b * G] = 1 << b
        for _ in range(D):
            new = reach.copy()
            for l in range(d):
                new |= reach[nbr[l]]
            if np.array_equal(new, reach):
                break
            reach = new
        cost = nb * N - int(_POP8[reach].sum()) + _PEN * dups()
        return cost, reach

    for l in range(d):
        for i in range(k):
            set_dart(l, i)
    cost, reach = evaluate()
    best = cost
    last = 0

    for t in range(iters):
        if cost == 0 or t - last > patience or time.monotonic() > deadline:
            break
        temp = max(0.3, 3.0 * (1.0 - t / iters))
        if k >= 2 and rng.random() < 0.25:
            # Swap the B-targets of two A-blocks in one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            p = pi[l]
            p[i1], p[i2] = p[i2], p[i1]
            set_dart(l, i1)
            set_dart(l, i2)
            c2, r2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                p[i1], p[i2] = p[i2], p[i1]
                set_dart(l, i1)
                set_dart(l, i2)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)
            old = S[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[l][i] = new
            set_dart(l, i)
            c2, r2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                S[l][i] = old
                set_dart(l, i)
        if cost < best:
            best, last = cost, t

    if cost != 0:
        return None
    A = nbr[:, :k * G].T.tolist()
    edges = [(u, v) for u, row in enumerate(A) for v in row]
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2 or d < 2:
        return best

    # Exact or known constructions with diameter 3.
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    # Ladder search: request vertex counts just above the current best.
    ks = (1, 1, 2, 2, 3, 4)
    while time.monotonic() < deadline:
        if best_n >= 3000:
            break
        k = rng.choice(ks)
        n_lo = best_n + 1
        n_hi = n_lo + max(2, best_n // 50)
        n_target = rng.randint(n_lo, n_hi)
        G = -(-n_target // (2 * k))
        if G < d or G > 1500:
            continue
        m, k2, r = _sample_group(G, rng)
        Gx, Ts, Invs = _group_tables(m, k2, r)
        res = _anneal(d, D, k, Gx, Ts, Invs, rng, deadline, 4000, 1000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
