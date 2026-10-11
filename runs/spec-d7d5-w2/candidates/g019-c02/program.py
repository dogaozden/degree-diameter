import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (exact constructions for small calibration cases).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A-block i with B-block layers[l][i] through voltage S[l][i]:
#   A_{i,g} ~ B_{layers[l][i], g*s}.
# Each layer is a permutation of blocks, so every vertex gets degree d.
#
# NEW in this version: iterated local search (ILS) on top of the annealer.
#   * _anneal returns the BEST state it visited, not the last one.
#   * When a run stalls, _perturb kicks the best state (re-randomise a few
#     voltages, maybe swap two B-targets) and anneals again from there.
#     Kicks are accepted only if they do not worsen the best cost.
#   * A per-group round cap keeps the bandit moving between groups.
#
# Other moves (kept from the parent): voltage move, layer-swap move, and
# defect-targeted voltage moves steered by the reach bitmasks.
# A bandit over base sizes k decides how much budget each k receives.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
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
    """Write layer l's neighbours for A-block i and B-block j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _build_nbr(d, k, G, Ts, Invs, layers, S):
    """Full neighbour table of shape (d, 2*k*G) for the given layer/voltage state."""
    nbr = np.empty((d, 2 * k * G), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])
    return nbr


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative block b is within distance D."""
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


def _cost(d, k, G, D, nbr, layers, S):
    """Return (cost, reach). Cost = unreached pairs + penalty per duplicated dart."""
    N = 2 * k * G
    reach = _reach(k, G, D, nbr, d)
    keys = set()
    dup = 0
    for l in range(d):
        for i in range(k):
            key = (i, layers[l][i], S[l][i])
            if key in keys:
                dup += 1
            else:
                keys.add(key)
    return _unreached(k, N, reach) + _PENALTY * dup, reach


def _accept(old, new, temp, rng):
    """Metropolis acceptance."""
    if new <= old:
        return True
    return rng.random() < math.exp(-(new - old) / temp)


def _anneal(d, D, k, G, Ts, Invs, st, rng, deadline, iters):
    """Simulated annealing from state st = (layers, S). Returns (best_cost, best_state)."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [row[:] for row in st[0]]
    S = [row[:] for row in st[1]]
    nbr = _build_nbr(d, k, G, Ts, Invs, layers, S)
    cost, reach = _cost(d, k, G, D, nbr, layers, S)
    best_cost = cost
    best = ([row[:] for row in layers], [row[:] for row in S])
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.02 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.25:
            # Layer-swap move: exchange B-targets of two A-blocks in one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2, r2 = _cost(d, k, G, D, nbr, layers, S)
            if _accept(cost, c2, temp, rng):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
        else:
            # Voltage move: defect-targeted with probability 0.4, otherwise uniform.
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
            c2, r2 = _cost(d, k, G, D, nbr, layers, S)
            if _accept(cost, c2, temp, rng):
                cost, reach = c2, r2
            else:
                S[l][i] = old
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

        if cost < best_cost:
            best_cost = cost
            best = ([row[:] for row in layers], [row[:] for row in S])

    return best_cost, best


def _random_state(d, k, G, rng):
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    return layers, S


def _perturb(st, d, k, G, rng):
    """Kick a state: re-randomise a few voltages, sometimes swap two B-targets."""
    layers = [row[:] for row in st[0]]
    S = [row[:] for row in st[1]]
    for _ in range(rng.randint(2, 6)):
        l = rng.randrange(d)
        i = rng.randrange(k)
        S[l][i] = rng.randrange(G)
    if k >= 2 and rng.random() < 0.3:
        l = rng.randrange(d)
        i1, i2 = rng.sample(range(k), 2)
        layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
    return layers, S


def _solve(d, D, k, G, Ts, Invs, rng, deadline):
    """ILS over one group. Returns (N, edges) when a valid lift is found, else None."""
    N = 2 * k * G
    st = _random_state(d, k, G, rng)
    c, st = _anneal(d, D, k, G, Ts, Invs, st, rng, deadline, 2500)
    rounds = 0
    while c > 0 and rounds < 12 and time.monotonic() < deadline:
        rounds += 1
        cand = _perturb(st, d, k, G, rng)
        c2, s2 = _anneal(d, D, k, G, Ts, Invs, cand, rng, deadline, 1500)
        if c2 <= c:
            c, st = c2, s2
    if c != 0:
        return None
    nbr = _build_nbr(d, k, G, Ts, Invs, st[0], st[1])
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.92 * time_limit, time_limit - 4.0))
    deadline = start + budget
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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: ILS over lifts, with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _solve(d, D, k, G, Ts, Invs, rng, deadline)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
