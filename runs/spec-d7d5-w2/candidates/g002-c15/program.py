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
# Bi-Cayley lifts over G = (Z_m x| Z_k2) x Z_t.
#
# NEW in this version:
#   * Direct factor Z_t: groups are no longer only semidirect products, so
#     orders such as 2*3*... with a cyclic direct part are reachable.
#   * Elite warm starts: good (low-cost) layer/voltage states from earlier
#     trials are kept. Half of the later trials perturb an elite state
#     (re-randomize a few voltages, maybe swap a layer) and re-anneal at a
#     lower temperature, instead of always restarting from random.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, t, r) for (Z_m x| Z_k2) x Z_t with m*k2*t >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        t = rng.choice([1, 1, 1, 2, 2, 3, 4])
        m = max(2, -(-target // (k2 * t)))
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
        return m, k2, t, r
    return None


def _tables(m, k2, r, t):
    """Return (G, Ts, Invs) for G = (Z_m x| Z_k2) x Z_t.

    Element x = ((a*k2) + b)*t + c. Ts[s, g] = g*s and Invs[s, h] = g with g*s = h.
    """
    G = m * k2 * t
    x = np.arange(G, dtype=np.int64)
    c = x % t
    b = (x // t) % k2
    a = x // (t * k2)
    powers = np.array([pow(r, e, m) for e in range(k2)], dtype=np.int64)
    pa = (a[:, None] + powers[b[:, None]] * a[None, :]) % m
    pb = (b[:, None] + b[None, :]) % k2
    pc = (c[:, None] + c[None, :]) % t
    M = (pa * k2 + pb) * t + pc  # M[x, y] = x * y
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g * s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _fill(nbr, k, G, Ts, Invs, L, S, d):
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, L[l][i], S[l][i])


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
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


def _search(d, D, k, tabs, rng, deadline, iters, L, S, frac):
    """Simulated annealing from the given state (L, S are modified in place).

    Returns (cost, L, S). cost == 0 means the lift has diameter <= D.
    """
    G, Ts, Invs = tabs
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    nbr = np.empty((d, N), dtype=np.int64)
    _fill(nbr, k, G, Ts, Invs, L, S, d)

    def dupcount():
        keys = [(i, L[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, frac * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            # Layer-swap move.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            L[l][i1], L[l][i2] = L[l][i2], L[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, L[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, L[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                L[l][i1], L[l][i2] = L[l][i2], L[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, L[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, L[l][i2], S[l][i2])
            continue

        # Voltage move: defect-targeted with probability 0.4, otherwise uniform.
        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = L[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, L[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, L[l][i], old)

    return cost, L, S


def _edges(d, k, tabs, L, S):
    G, Ts, Invs = tabs
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    _fill(nbr, k, G, Ts, Invs, L, S, d)
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


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

    # Table cache keyed by group parameters.
    cache = {}

    def get_tabs(params):
        if params not in cache:
            if len(cache) > 48:
                cache.clear()
            m, k2, r, t = params
            cache[params] = _tables(m, k2, r, t)
        return cache[params]

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    elite = []  # low-cost states, each with its own group and base size

    while time.monotonic() < deadline:
        # Drop elites that can no longer beat the current best.
        elite = [e for e in elite if 2 * e["k"] * e["G"] > best_n]

        use_elite = bool(elite) and rng.random() < 0.5
        if use_elite:
            e = rng.choice(elite)
            k, params, G = e["k"], e["params"], e["G"]
            tabs = get_tabs(params)
            L = [list(row) for row in e["L"]]
            S = [list(row) for row in e["S"]]
            # Perturb: re-randomize a few voltages, sometimes swap one layer.
            for _ in range(3):
                l = rng.randrange(d)
                i = rng.randrange(k)
                S[l][i] = rng.randrange(G)
            if k >= 2 and rng.random() < 0.5:
                l = rng.randrange(d)
                i1, i2 = rng.sample(range(k), 2)
                L[l][i1], L[l][i2] = L[l][i2], L[l][i1]
            cost, L, S = _search(d, D, k, tabs, rng, deadline, 8000, L, S, 0.004)
        else:
            k = pick_k()
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, t, r = g
            params = (m, k2, r, t)
            tabs = get_tabs(params)
            G = tabs[0]
            if 2 * k * G <= best_n:
                continue
            L = [rng.sample(range(k), k) for _ in range(d)]
            S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
            trials[k] += 1
            cost, L, S = _search(d, D, k, tabs, rng, deadline, 20000, L, S, 0.02)
            if cost == 0:
                wins[k] += 1

        if cost == 0:
            n_, e_ = _edges(d, k, tabs, L, S)
            consider(n_, e_)

        elite.append({"k": k, "params": params, "G": G, "L": L, "S": S, "cost": cost})
        elite.sort(key=lambda e: e["cost"])
        del elite[8:]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
