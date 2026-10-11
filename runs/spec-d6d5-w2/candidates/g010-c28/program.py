import math
import random
import time

import numpy as np

import lib

BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Group multiplication tables (vectorised). Element (a, b) of Z_m x| Z_k2 is
# coded a*k2 + b with product (a + r^b c, b + d); identity is code 0.
# ----------------------------------------------------------------------------

def _mul_cyclic(G):
    a = np.arange(G, dtype=np.int64)
    return (a[:, None] + a[None, :]) % G


def _mul_semidirect(m, k2, r):
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    pw = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    return ((A + pw[B] * C) % m) * k2 + (B + Dd) % k2


def _sample_mul(G, rng):
    ks = [k2 for k2 in range(2, 13) if G % k2 == 0 and G // k2 >= 2]
    if not ks or rng.random() < 0.3:
        return _mul_cyclic(G)
    k2 = rng.choice(ks)
    m = G // k2
    cands = [r for r in range(1, m)
             if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not cands:
        return _mul_cyclic(G)
    return _mul_semidirect(m, k2, rng.choice(cands))


# ----------------------------------------------------------------------------
# Bi-Cayley lifts with k base vertices per side and d layers.
# Layer L matches A_i to B_{p[L,i]} with voltage volt[L,i]:
#   A_i,g ~ B_{p[L,i]}, g*s.  Left translation by the group is an automorphism,
# so distances from one representative per base vertex decide the diameter.
# ----------------------------------------------------------------------------

def _lift_nb(k, d, G, M, p, volt):
    """Neighbour array (2kG, d) of the lift, or None if some vertex gets a repeated edge."""
    code = p * G + volt                       # (d, k)
    cs = np.sort(code.T, axis=1)              # (k, d)
    if np.any(cs[:, 1:] == cs[:, :-1]):
        return None
    vT = volt.T                               # (k, d)
    pT = p.T
    nbA = ((k + pT)[None, :, :] * G + M[:, vT]).transpose(1, 0, 2).reshape(k * G, d)
    src = np.repeat(np.arange(k * G, dtype=np.int64), d)
    dst = nbA.ravel()
    order = np.argsort(dst, kind="stable")
    nbB = src[order].reshape(k * G, d)
    return np.vstack([nbA, nbB])


def _cost(nb, reps, D):
    """Total number of (representative, vertex) pairs at distance > D."""
    N = nb.shape[0]
    d = nb.shape[1]
    R = len(reps)
    visited = np.zeros((R, N), dtype=bool)
    visited[np.arange(R), reps] = True
    frontier = visited.copy()
    for _ in range(D):
        rr, vv = np.nonzero(frontier)
        if rr.size == 0:
            break
        nxt = np.zeros((R, N), dtype=bool)
        nxt[np.repeat(rr, d), nb[vv].ravel()] = True
        nxt &= ~visited
        visited |= nxt
        frontier = nxt
    return R * N - int(visited.sum())


def _anneal(k, d, G, M, D, rng, deadline, iters):
    """Anneal voltages and layer permutations. Returns (cost, p, volt)."""
    reps = np.array([i * G for i in range(k)] + [(k + j) * G for j in range(k)],
                    dtype=np.int64)
    p = np.zeros((d, k), dtype=np.int64)
    volt = np.zeros((d, k), dtype=np.int64)

    def randomise():
        for L in range(d):
            p[L] = rng.sample(range(k), k)
            for i in range(k):
                volt[L, i] = rng.randrange(G)

    def ev():
        nb = _lift_nb(k, d, G, M, p, volt)
        if nb is None:
            return BIG
        return _cost(nb, reps, D)

    cur = BIG
    for _ in range(50):
        randomise()
        cur = ev()
        if cur < BIG:
            break
    if cur >= BIG:
        return BIG, p, volt

    for it in range(iters):
        if cur == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        T = 1.5 * (0.1 ** (it / iters))
        if k > 1 and rng.random() < 0.25:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            p[L, a], p[L, b] = p[L, b], p[L, a]
            new = ev()
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                p[L, a], p[L, b] = p[L, b], p[L, a]
        else:
            L = rng.randrange(d)
            a = rng.randrange(k)
            old = int(volt[L, a])
            nv = rng.randrange(G)
            if nv == old:
                continue
            volt[L, a] = nv
            new = ev()
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                volt[L, a] = old
    return cur, p, volt


def _edges_from(k, d, G, M, p, volt):
    nb = _lift_nb(k, d, G, M, p, volt)
    E = []
    for a in range(k * G):
        for b in nb[a]:
            E.append((a, int(b)))
    return 2 * k * G, E


# ----------------------------------------------------------------------------
# Baselines.
# ----------------------------------------------------------------------------

def _baselines(d, D):
    out = []
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            out.append(lib.araujo_lopez_graph(q))
        except Exception:
            pass
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    main_deadline = start + 0.80 * time_limit

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D == 2 or best_n >= lib.moore_bound(d, D):
        return best_n, best_E

    if D >= 3:
        for n_c, e_c in _baselines(d, D):
            consider(n_c, e_c)

    rng = random.Random(seed)
    while time.monotonic() < main_deadline - 0.5:
        if best_n >= lib.moore_bound(d, D):
            break
        k = rng.choice([1, 1, 1, 2, 2, 3, 4])
        lo = best_n // (2 * k) + 1
        G = lo + rng.randrange(0, lo // 10 + 2)
        if G < 2:
            continue
        M = _sample_mul(G, rng)
        slice_deadline = min(main_deadline, time.monotonic() + 3.0)
        cost, p, volt = _anneal(k, d, G, M, D, rng, slice_deadline, 40000)
        if cost == 0:
            n, E = _edges_from(k, d, G, M, p, volt)
            consider(n, E)

    if not lib.is_valid(best_n, best_E, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_E
