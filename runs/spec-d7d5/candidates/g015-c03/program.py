import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d.
#
# Routines:
#   _semidirect_tables: group tables by one numpy broadcast.
#   bandit over base sizes k (success-rate score).
#   _structured_init: geometric-progression voltages y_i * x^(l+1).
#
# NEW routine: elite-pool iterated local search (ILS).
#   Annealing runs that end with cost > 0 are kept in a small pool, keyed by
#   their group and base size. Later runs, with some probability, restart from
#   a pool member: a few voltages are re-randomized (a kick) and annealing
#   resumes at a lower temperature. Fresh restarts still happen, so the search
#   keeps global diversity while exploiting near-solutions.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_ILS_PROB = 0.5
_POOL_MAX = 12
_ILS_ITERS = 3000
_FRESH_ITERS = 4000


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
        if k2 == 1:
            r = 1
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

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h, built with one numpy broadcast.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = M[g, s] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _structured_init(d, k, G, Ts, rng):
    """Geometric-progression start: layers[l][i] = (i + l) mod k, S[l][i] = y_i * x^(l+1)."""
    x = rng.randrange(1, G)
    powers = [0]  # identity element is index 0
    for _ in range(d):
        powers.append(int(Ts[x, powers[-1]]))
    ys = [rng.randrange(G) for _ in range(k)]
    layers = [[(i + l) % k for i in range(k)] for l in range(d)]
    S = [[int(Ts[ys[i], powers[l + 1]]) for i in range(k)] for l in range(d)]
    return layers, S


def _random_init(d, k, G, rng):
    """Uniform start: random permutation per layer and random voltages."""
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    return layers, S


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _nbr_from(d, k, G, Ts, Invs, layers, S):
    """Build the (d, 2kG) neighbour table for the given layers and voltages."""
    nbr = np.empty((d, 2 * k * G), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])
    return nbr


def _dupcount(d, k, layers, S):
    keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
    return len(keys) - len(set(keys))


def _cost(k, G, D, nbr):
    """Unreached (representative, vertex) pairs over all 2k representatives.

    Bit b of reach[v] is set when representative block b is within distance t of v.
    Left multiplication is an automorphism, so the 2k block starts cover all orbits.
    """
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


def _anneal(d, D, k, G, Ts, Invs, layers, S, rng, deadline, iters, c0=None):
    """Simulated annealing over voltages and per-layer target swaps.

    layers and S are mutated in place and end in the last accepted state.
    Returns the final cost (0 means a valid lift was found).
    """
    nbr = _nbr_from(d, k, G, Ts, Invs, layers, S)

    def full_cost():
        return _cost(k, G, D, nbr) + _PENALTY * _dupcount(d, k, layers, S)

    cost = full_cost()
    if c0 is None:
        c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)

        if k > 1 and rng.random() < _SWAP_PROB:
            # Structural move: swap the B-side targets of two base vertices in layer l.
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = full_cost()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        # Voltage move.
        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = full_cost()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)
    return cost


def _edges_from(k, G, nbr):
    """Edge list of the lift: every A-side vertex with all its neighbours, deduplicated."""
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return sorted(edges)


def _kick(d, k, G, layers, S, rng):
    """Perturb an elite state: re-randomize a few voltages and occasionally a layer's permutation."""
    for _ in range(max(1, k // 2 + 1)):
        l = rng.randrange(d)
        i = rng.randrange(k)
        S[l][i] = rng.randrange(G)
    if rng.random() < 0.2:
        l = rng.randrange(d)
        if k > 1:
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately (calibration-style cases).
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

    # Main search: bandit over base sizes k, with an elite pool for ILS restarts.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    pool = []  # entries: dict(cost, k, params, layers, S)

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        elites = [e for e in pool if e["k"] == k]
        use_ils = bool(elites) and rng.random() < _ILS_PROB

        if use_ils:
            # Pick a good elite (lowest cost, with noise) and restart it with a kick.
            e = min(elites, key=lambda e: e["cost"] * (1.0 + 0.5 * rng.random()))
            m, k2, r = e["params"]
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            if 2 * k * G <= best_n:
                pool.remove(e)
                continue
            layers = [row[:] for row in e["layers"]]
            S = [row[:] for row in e["S"]]
            _kick(d, k, G, layers, S, rng)
            c0 = max(1.0, 0.2 * float(max(e["cost"], 1)))
            iters = _ILS_ITERS
            params = e["params"]
        else:
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            if 2 * k * G <= best_n:
                continue
            if rng.random() < _STRUCT_PROB:
                layers, S = _structured_init(d, k, G, Ts, rng)
            else:
                layers, S = _random_init(d, k, G, rng)
            c0 = None
            iters = _FRESH_ITERS
            params = g

        trials[k] += 1
        cost = _anneal(d, D, k, G, Ts, Invs, layers, S, rng, deadline, iters, c0)

        if cost == 0:
            wins[k] += 1
            nbr = _nbr_from(d, k, G, Ts, Invs, layers, S)
            consider(2 * k * G, _edges_from(k, G, nbr))
            if use_ils:
                pool.remove(e)
        else:
            if use_ils:
                # Update the elite in place with the new (possibly better) state.
                if cost <= e["cost"]:
                    e.update(cost=cost, layers=layers, S=S)
                else:
                    pool.remove(e)
            else:
                pool.append({"cost": cost, "k": k, "params": params,
                             "layers": layers, "S": S})
                if len(pool) > _POOL_MAX:
                    pool.sort(key=lambda x: x["cost"])
                    del pool[_POOL_MAX:]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
