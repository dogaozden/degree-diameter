import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Lifts over finite groups, built from explicit multiplication tables.
#
# A base graph has k vertices on each side. Vertices are A_{i,x} = i*G + x and
# B_{p,y} = (k+p)*G + y. Layer l joins A_i to B_{perm_l(i)} with voltage s, so
# A_{i,x} ~ B_{p, x*s}. Every layer is a permutation, so every vertex has degree
# exactly d and the graph is bipartite. Left multiplication is an automorphism,
# so diameter only needs checking from the k A-block and k B-block representatives.
#
# Groups are direct products Z_a x Z_b, semidirect products Z_m x| Z_k (which
# includes dihedral groups), and cyclic groups. Search is iterated local search:
# simulated annealing that falls back to the best state with a small perturbation
# when it stagnates, rather than restarting from scratch.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (2, 3, 4, 5, 6, 7, 8)  # 2k bits must fit the reach masks (2k <= 16)


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_abelian(a, b):
    """Z_a x Z_b, element p*b + q, identity 0. Returns (G, multiplication table)."""
    G = a * b
    x = np.arange(G, dtype=np.int64)
    p, q = x[:, None] // b, x[:, None] % b
    p2, q2 = x[None, :] // b, x[None, :] % b
    M = ((p + p2) % a) * b + (q + q2) % b
    return G, M


def _group_semidirect(m, k, r):
    """Z_m x| Z_k, element a*k + b, (a,b)(c,e) = (a + r^b c, b + e). Requires r^k = 1 mod m."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a, b = x // k, x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b[:, None]] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return G, M


def _sample_group(lo, rng):
    """Random group with order >= lo, as (G, M). Returns None if sampling fails."""
    for _ in range(400):
        if rng.random() < 0.35:
            b = rng.choice((2, 3, 4, 5, 6, 7, 8, 9, 10, 12))
            a = max(2, -(-lo // b))
            return _group_abelian(a, b)
        k2 = rng.choice((2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16))
        m = max(3, -(-lo // k2))
        cands = [1] + ([m - 1] if k2 == 2 else []) + [rng.randrange(2, m) for _ in range(30)]
        rng.shuffle(cands)
        for c in cands:
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                return _group_semidirect(m, k2, c)
    return None


def _set_dart(nbr, k, G, Ts, Invs, l, i, p, s):
    """Write layer l's neighbours for A-block i (target B-block p, voltage s) and the reverse."""
    nbr[l, i * G:(i + 1) * G] = (k + p) * G + Ts[s]
    nbr[l, (k + p) * G:(k + p + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when the representative of block b is within distance D."""
    N = nbr.shape[1]
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
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _anneal(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Iterated local search over voltages and layer permutations. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def rebuild():
        for l in range(d):
            for i in range(k):
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dup():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    def score():
        reach = _reach(k, G, D, nbr, d)
        return _unreached(k, N, reach) + _PENALTY * dup(), reach

    rebuild()
    cost, reach = score()
    best_cost = cost
    best_state = ([r[:] for r in layers], [s[:] for s in S])
    c0 = float(max(cost, 1))
    last = 0

    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            # Return to the best state and perturb a few voltages.
            layers = [r[:] for r in best_state[0]]
            S = [s[:] for s in best_state[1]]
            rebuild()
            for _ in range(3):
                l = rng.randrange(d)
                i = rng.randrange(k)
                S[l][i] = rng.randrange(G)
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])
            cost, reach = score()
            last = t
            continue

        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.25:
            # Layer-swap move: exchange the B-targets of two A-blocks in one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2, r2 = score()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
        else:
            # Voltage move, defect-targeted with probability 0.4.
            bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else []
            if len(bad):
                u = int(bad[rng.randrange(len(bad))])
                block = u // G
                l = rng.randrange(d)
                if block < k:
                    i = block
                else:
                    i = layers[l].index(block - k)
            else:
                l = rng.randrange(d)
                i = rng.randrange(k)
            old = S[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[l][i] = new
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
            c2, r2 = score()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                S[l][i] = old
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

        if cost < best_cost:
            best_cost = cost
            best_state = ([r[:] for r in layers], [s[:] for s in S])
            last = t

    if best_cost != 0:
        return None
    layers = [r[:] for r in best_state[0]]
    S = [s[:] for s in best_state[1]]
    rebuild()
    us = np.repeat(np.arange(k * G, dtype=np.int64), d)
    vs = nbr[:, :k * G].T.ravel()
    return N, list(zip(us.tolist(), vs.tolist()))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions for small D.
    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: lifts over groups with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        lo = best_n // (2 * k) + 1  # ensures 2*k*G > best_n
        g = _sample_group(lo, rng)
        if g is None:
            continue
        G, M = g
        if 2 * k * G <= best_n:
            continue
        inv = np.argmax(M == 0, axis=1)
        Ts = np.ascontiguousarray(M.T)           # Ts[s, x] = x*s
        Invs = np.ascontiguousarray(M[:, inv].T)  # Invs[s, y] = y*s^{-1}
        trials[k] += 1
        res = _anneal(d, D, k, G, Ts, Invs, rng, deadline, 6000, 1500)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
