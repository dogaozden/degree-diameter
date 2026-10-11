import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Number-theory helpers.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _primitive_root(p):
    """Primitive root modulo an odd prime p."""
    phi = p - 1
    factors = []
    x = phi
    f = 2
    while f * f <= x:
        if x % f == 0:
            factors.append(f)
            while x % f == 0:
                x //= f
        f += 1
    if x > 1:
        factors.append(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in factors):
            return g
    return 1


# ----------------------------------------------------------------------------
# Group right-multiplication tables: RT[s, g] = g * s, identity at index 0.
# Left multiplication is an automorphism of the bi-Cayley graph built from RT.
# ----------------------------------------------------------------------------

def _semi_RT(m, k, r):
    """Z_m x|_r Z_k with (a1,b1)(a2,b2) = (a1 + r^{b1} a2, b1 + b2); element (a,b) coded a*k+b."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    A = idx // k
    B = idx % k
    powr = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    PB = powr[B]
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        c, dd = divmod(s, k)
        RT[s] = ((A + PB * c) % m) * k + (B + dd) % k
    return RT


def _affine_RT(p, t):
    """Affine group {x -> a x + b over Z_p : a in H}, |H| = t, t | p-1. Element (a,b) coded pos(a)*p + b."""
    g0 = _primitive_root(p)
    h = pow(g0, (p - 1) // t, p)
    H = [pow(h, j, p) for j in range(t)]
    pos = np.full(p, -1, dtype=np.int64)
    for i, v in enumerate(H):
        pos[v] = i
    G = p * t
    idx = np.arange(G, dtype=np.int64)
    Hv = np.array(H, dtype=np.int64)
    A = Hv[idx // p]
    B = idx % p
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        a2 = H[s // p]
        b2 = s % p
        na = (A * a2) % p
        nb = (A * b2 + B) % p
        RT[s] = pos[na] * p + nb
    return RT


def _sample_group(target, rng):
    """Return (RT, G) for a random group of order G >= target (roughly), or None."""
    for _ in range(200):
        if rng.random() < 0.35:
            t = rng.choice([2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24])
            p0 = max(3, -(-target // t))
            for p in range(p0, p0 + 300):
                if _is_prime(p) and (p - 1) % t == 0:
                    return _affine_RT(p, t), p * t
            continue
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            if m > 2:
                for _ in range(80):
                    c = rng.randrange(2, m)
                    if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                        r = c
                        break
            if r is None:
                continue
        return _semi_RT(m, k2, r), m * k2
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts: k base vertices per side, d layers. Layer l pairs A-vertex i
# with B-vertex layers[l][i] through voltage S[l][i]:
#   A_{i,g} ~ B_{j,g*s},  B_{j,h} ~ A_{i,g} where g*s = h.
# Cost = unreached (block representative, vertex) pairs, evaluated with
# bit-parallel propagation over the 2k block representatives.
# ----------------------------------------------------------------------------

def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    d, N = nbr.shape
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, RT, rng, deadline, iters):
    """Simulated annealing over voltages. Returns (n, edges) with diameter <= D, or None."""
    Ts = RT
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.arange(G)[None, :]
    N = 2 * k * G

    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    cost = _cost(k, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is a valid fallback for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2 or d <= 1:
        return best

    if d == 2:
        # Even cycle of length 2D: bipartite, diameter D, order 2D (Moore bound).
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # D >= 3, d >= 3.
    if D == 3:
        for q in range(min(d - 1, 40), 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2) and not lib.is_prime_power(d - 1):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except ValueError:
                pass
        if lib.is_prime_power(d - 1):
            return best

    # Main search: bi-Cayley lifts over groups with 1-6 base vertices per side.
    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 3, 4, 5, 6])
        target = best_n // (2 * k) + 1 + rng.randrange(0, max(2, best_n // (16 * k) + 2))
        g = _sample_group(max(2, target), rng)
        if g is None:
            continue
        RT, G = g
        if 2 * k * G <= best_n:
            continue
        res = _search(d, D, k, G, RT, rng, deadline, 4000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
