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
#
# Search stages per group:
#   1. simulated annealing (voltage, layer-swap, defect-targeted moves),
#   2. NEW: exhaustive coordinate descent. For one dart at a time, every
#      possible voltage in the group is scored and the best one is kept.
#   3. NEW: iterated local search. Perturb a few darts of the best local
#      optimum, re-descend, and keep the result if it is no worse.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_CD_CANDIDATES = 300  # cap on voltages scored per dart in coordinate descent


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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _apply_all(nbr, k, G, Ts, Invs, layers, S, d):
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])


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
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _dup(layers, S, k, d):
    keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
    return len(keys) - len(set(keys))


def _full_cost(k, G, D, d, nbr, layers, S):
    N = 2 * k * G
    reach = _reach(k, G, D, nbr, d)
    return _unreached(k, N, reach) + _PENALTY * _dup(layers, S, k, d), reach


# ----------------------------------------------------------------------------
# NEW helper: exhaustive single-dart voltage optimisation.
# ----------------------------------------------------------------------------

def _best_voltage_for_dart(d, D, k, G, Ts, Invs, layers, S, nbr, l, i, rng, cur_cost):
    """Set dart (l, i) to the voltage that minimises the cost. Returns the resulting cost."""
    old = S[l][i]
    best_c, best_s = cur_cost, old
    cands = range(G) if G <= _CD_CANDIDATES else rng.sample(range(G), _CD_CANDIDATES)
    for s in cands:
        if s == old:
            continue
        S[l][i] = s
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], s)
        c, _ = _full_cost(k, G, D, d, nbr, layers, S)
        if c < best_c:
            best_c, best_s = c, s
            if c == 0:
                break
    S[l][i] = best_s
    _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], best_s)
    return best_c


def _coord_descent(d, D, k, G, Ts, Invs, layers, S, nbr, rng, deadline):
    """Repeat single-dart exhaustive optimisation until no dart improves. Returns the cost."""
    cost, _ = _full_cost(k, G, D, d, nbr, layers, S)
    darts = [(l, i) for l in range(d) for i in range(k)]
    improved = True
    while improved and cost > 0 and time.monotonic() < deadline:
        improved = False
        rng.shuffle(darts)
        for l, i in darts:
            if time.monotonic() > deadline or cost == 0:
                break
            old = S[l][i]
            c = _best_voltage_for_dart(d, D, k, G, Ts, Invs, layers, S, nbr, l, i, rng, cost)
            if S[l][i] != old:
                cost = c
                improved = True
    return cost


def _snapshot(layers, S, d, k):
    return ([row[:] for row in layers], [row[:] for row in S])


def _restore(layers, S, snap, d):
    for l in range(d):
        layers[l][:] = snap[0][l]
        S[l][:] = snap[1][l]


def _ils(d, D, k, G, Ts, Invs, layers, S, nbr, rng, deadline):
    """Iterated local search on top of coordinate descent. Returns the best cost found."""
    cost = _coord_descent(d, D, k, G, Ts, Invs, layers, S, nbr, rng, deadline)
    best_cost = cost
    best_snap = _snapshot(layers, S, d, k)
    while best_cost > 0 and time.monotonic() < deadline:
        _restore(layers, S, best_snap, d)
        for _ in range(rng.randint(1, 3)):
            l = rng.randrange(d)
            i = rng.randrange(k)
            S[l][i] = rng.randrange(G)
        _apply_all(nbr, k, G, Ts, Invs, layers, S, d)
        cost = _coord_descent(d, D, k, G, Ts, Invs, layers, S, nbr, rng, deadline)
        if cost < best_cost:
            best_cost = cost
            best_snap = _snapshot(layers, S, d, k)
    _restore(layers, S, best_snap, d)
    _apply_all(nbr, k, G, Ts, Invs, layers, S, d)
    return best_cost


def _search(d, D, k, G, Ts, Invs, rng, sa_deadline, ils_deadline, iters):
    """Annealing, then coordinate descent / ILS. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    _apply_all(nbr, k, G, Ts, Invs, layers, S, d)

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * _dup(layers, S, k, d)
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > sa_deadline:
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
            c2 = _unreached(k, N, r2) + _PENALTY * _dup(layers, S, k, d)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
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
        c2 = _unreached(k, N, r2) + _PENALTY * _dup(layers, S, k, d)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    # Refinement phase: exhaustive descent and ILS from the annealed state.
    if cost != 0 and time.monotonic() < ils_deadline:
        _ils(d, D, k, G, Ts, Invs, layers, S, nbr, rng, ils_deadline)

    final, _ = _full_cost(k, G, D, d, nbr, layers, S)
    if final != 0:
        return None
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

    # Main search with a bandit over base sizes k.
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

        # Per-trial window: annealing gets half, refinement gets the rest.
        now = time.monotonic()
        slice_end = min(deadline, now + 8.0)
        sa_deadline = now + 0.5 * (slice_end - now)
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, sa_deadline, slice_end, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
