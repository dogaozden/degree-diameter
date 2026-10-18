"""Bi-Cayley lift search with a new warm-start growth move.

Changes from the parent:
- Lift search keeps the voltage state of every success. A new "grow" move takes the
  largest lift found so far and adds one base pair per side over the same group.
  Each layer splices the new pair in with one old dart, so every vertex keeps degree d.
  The annealer then repairs the diameter starting from that state. This gives order
  steps of 2G instead of cold restarts.
- The C grow-by-two phase is dropped. The parent skipped it whenever the graph had
  more than 1500 vertices, which covers the d11 D5 target, so it never ran there.
- Each lift stage is guarded, and every returned graph is checked with lib.is_valid.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)
_KMAX = 6  # reach bitmasks use 2k <= 12 bits, which fits the popcount table


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Layer l joins A-block i to B-block j with voltage s (A_{i,g} ~ B_{j,g*s})."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when the representative of block b is within distance D.

    Left multiplication by a group element is an automorphism, so the representatives
    (group identity in each block) decide the whole diameter condition.
    """
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience, init=None):
    """Simulated annealing over layer permutations and voltages.

    Returns (n, edges, (layers, S)) on success, or None. `init` = (layers, S) is an
    optional warm start with the same k.
    """
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    if init is None:
        layers = [rng.sample(range(k), k) for _ in range(d)]
        S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    else:
        layers = [list(x) for x in init[0]]
        S = [list(x) for x in init[1]]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
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
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges), (layers, S)


def _grow_state(d, k, G, state, rng):
    """Warm start with k+1 base pairs: in each layer, splice new pair (A_k, B_k) into one old dart.

    Old dart A_i - B_j (voltage s) becomes A_i - B_k (fresh voltage) and A_k - B_j (voltage s).
    Each layer stays a perfect matching, so degrees remain d.
    """
    layers, S = state
    nl, ns = [], []
    for l in range(d):
        L = list(layers[l])
        V = list(S[l])
        i = rng.randrange(k)
        j, s = L[i], V[i]
        L[i], V[i] = k, rng.randrange(G)
        L.append(j)
        V.append(s)
        nl.append(L)
        ns.append(V)
    return nl, ns


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.9 * time_limit - 1.5)
    deadline = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Lift search: random bandit over base sizes, plus warm-started growth from the largest lift.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05
    lift_best = None  # (n, k, G, Ts, Invs, state)

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        try:
            grew = False
            if lift_best is not None and rng.random() < 0.5:
                _, k, G, Ts, Invs, state = lift_best
                if k < _KMAX and 2 * (k + 1) * G <= goal * 1.15:
                    grew = True
                    init = _grow_state(d, k, G, state, rng)
                    res = _search(d, D, k + 1, G, Ts, Invs, rng, deadline, 3000, 800, init)
                    if res is not None:
                        consider(res[0], res[1])
                        goal = max(goal, res[0] * 1.04)
                        lift_best = (res[0], k + 1, G, Ts, Invs, res[2])
            if grew:
                continue

            k = pick_k()
            target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
            g = _sample_group(target, rng)
            if g is None:
                goal = max(float(best_n) * 1.02, goal * 0.99)
                continue
            m, k2, r = g
            if m * k2 > 4000:  # keeps the G x G tables small
                continue
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            if 2 * k * G <= best_n:
                goal = max(goal, best_n * 1.02)
                continue
            trials[k] += 1
            res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])
                goal = max(goal, res[0] * 1.04)
                if lift_best is None or res[0] > lift_best[0]:
                    lift_best = (res[0], k, G, Ts, Invs, res[2])
            else:
                goal = max(float(best_n) * 1.02, goal * 0.99)
        except Exception:
            # A failed stage must not lose the valid graph found so far.
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
