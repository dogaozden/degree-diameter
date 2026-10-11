import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Constants and small helpers.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x| Z_k2 (base graphs for the 2-lift stage).
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h. Each layer is a
# permutation, so every vertex has degree d exactly.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type multiplier
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
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = g with g*s = h."""
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
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex over the 2k block representatives within distance D."""
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over bi-Cayley layers and voltages. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
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
    return N, sorted(edges)


def _base_from_bicayley(d, D, goal, rng, deadline):
    """Find a valid bi-Cayley graph with at least `goal` vertices, or None."""
    for _ in range(60):
        if time.monotonic() > deadline:
            break
        k = rng.choice(_KS)
        target = max(2, -(-goal // (2 * k)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            return res
    return None


# ----------------------------------------------------------------------------
# NEW: signed 2-lift search.
#
# Given a base graph H (n vertices, bipartite, max degree d), the 2-lift has
# vertices (u, i) = 2u + i and, for each base edge e = (u, v) with sign s_e in
# {0, 1}, the lifted edges (u, i) - (v, i XOR s_e). The pulled-back colouring
# c'(u, i) = c(u) keeps the lift bipartite, and degrees are preserved.
#
# We search the sign vector by simulated annealing on the number of unreached
# ordered pairs within distance D. Reachability is held as packed uint64
# bitsets (N x W words) and each evaluation is D*d row gathers, so a few
# thousand evaluations per second are possible at N about 1200.
# Flipping one sign only rewrites 4 neighbour entries.
# ----------------------------------------------------------------------------

def _two_lift(n, edges, d, D, rng, deadline):
    """Search signs for a 2-lift of diameter <= D. Returns (N, edges) or None."""
    E = len(edges)
    if E == 0:
        return None
    N = 2 * n
    W = (N + 63) // 64
    deg = [0] * n
    slot_edge = np.full((n, d), -1, dtype=np.int64)
    eu, ev, elu, elv = [], [], [], []
    for e, (u, v) in enumerate(edges):
        if deg[u] >= d or deg[v] >= d:
            return None
        eu.append(u)
        ev.append(v)
        elu.append(deg[u])
        elv.append(deg[v])
        slot_edge[u, deg[u]] = e
        slot_edge[v, deg[v]] = e
        deg[u] += 1
        deg[v] += 1

    idx = np.arange(N, dtype=np.int64)
    base_reach = np.zeros((N, W), dtype=np.uint64)
    base_reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    nbr = np.tile(idx, (d, 1))  # padded slots point to self (harmless in OR)

    def set_sign(e, s):
        u, v, lu, lv = eu[e], ev[e], elu[e], elv[e]
        nbr[lu, 2 * u] = 2 * v + s
        nbr[lu, 2 * u + 1] = 2 * v + (1 - s)
        nbr[lv, 2 * v] = 2 * u + s
        nbr[lv, 2 * v + 1] = 2 * u + (1 - s)

    def reach_of():
        reach = base_reach
        for _ in range(D):
            new = reach.copy()
            for l in range(d):
                new |= reach[nbr[l]]
            if np.array_equal(new, reach):
                break
            reach = new
        return reach

    def evaluate():
        reach = reach_of()
        rp = _POP8[reach.view(np.uint8)].sum(axis=1)
        return reach, rp, N * N - int(rp.sum())

    sign = [rng.randrange(2) for _ in range(E)]
    for e in range(E):
        set_sign(e, sign[e])
    _, rp, cost = evaluate()
    best_cost = cost
    best_sign = list(sign)
    stall = 0

    while cost > 0:
        if time.monotonic() > deadline:
            return None
        T = max(2.0, 0.01 * cost)

        # Proposal: an edge at the most-deficient vertex, a random vertex, or a random edge.
        if rng.random() < 0.5:
            x = int(np.argmax(N - rp)) if rng.random() < 0.5 else rng.randrange(N)
            u = x >> 1
            e = int(slot_edge[u, rng.randrange(d)])
            if e < 0:
                e = rng.randrange(E)
        else:
            e = rng.randrange(E)

        s_new = 1 - sign[e]
        set_sign(e, s_new)
        r2, rp2, c2 = evaluate()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            sign[e] = s_new
            rp, cost = rp2, c2
            if cost < best_cost:
                best_cost = cost
                best_sign = list(sign)
                stall = 0
            else:
                stall += 1
        else:
            set_sign(e, sign[e])
            stall += 1

        if stall > 2500:
            # Restart from a perturbed copy of the best sign vector.
            sign = list(best_sign)
            for _ in range(max(2, E // 40)):
                f = rng.randrange(E)
                sign[f] ^= 1
            for e2 in range(E):
                set_sign(e2, sign[e2])
            _, rp, cost = evaluate()
            stall = 0

    out = []
    for e in range(E):
        u, v, s = eu[e], ev[e], sign[e]
        out.append((2 * u, 2 * v + s))
        out.append((2 * u + 1, 2 * v + 1 - s))
    return N, out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.88 * time_limit, time_limit - 6.0))
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

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d < 3:
        return best

    mb = lib._moore_bound(d, D)
    # Lift target: 2-lift of a base of size ~0.185*Moore gives ~0.37*Moore,
    # which is about the record for d=7, D=5.
    goal = max(best_n // 2 + 1, int(0.185 * mb))

    while time.monotonic() < deadline:
        now = time.monotonic()
        base = _base_from_bicayley(
            d, D, goal + rng.randrange(0, max(2, mb // 200)), rng, min(deadline, now + 8.0)
        )
        if base is None:
            goal = max(best_n // 2 + 1, int(goal * 0.97))
            continue

        now = time.monotonic()
        lift_end = min(deadline, now + max(6.0, min(20.0, 0.5 * (deadline - now))))
        lifted = _two_lift(base[0], base[1], d, D, rng, lift_end)
        if lifted is not None and lifted[0] > best_n:
            before = best_n
            consider(lifted[0], lifted[1])
            if best_n > before:
                goal = best_n // 2 + 1 + rng.randrange(0, max(2, best_n // 40))
                continue
        goal = max(best_n // 2 + 1, int(goal * 0.98))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
