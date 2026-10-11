import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact families (used as fallbacks and for calibration cases).
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
# Bi-Cayley lifts over groups Z_m x| Z_k2, searched by iterated local search.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p, g*s}.
# Every layer is a permutation, so every vertex has degree d. Left multiplication
# is an automorphism, so the diameter test only needs 2k representative vertices.
#
# Search engine (different from annealing): coordinate-wise best-improvement.
# For every (layer, block) coordinate, a sample of candidate voltages is scored
# exactly, the best one is kept (plateau moves allowed), and sweeps repeat.
# When sweeps stall, the search perturbs the best state with random voltage
# resets and layer swaps (iterated local search).
#
# Targets are chosen by a goal order that starts at a fraction of the Moore
# bound and climbs as valid graphs are found. Every result is checked with
# lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


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
    """Write layer l's neighbours for A-block i and B-block j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


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


def _ils(d, D, k, G, Ts, Invs, rng, deadline):
    """Iterated local search over voltages and layer assignments. Returns (n, edges) or None."""
    N = 2 * k * G
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def setd(l, i):
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    for l in range(d):
        for i in range(k):
            setd(l, i)

    def dupcount():
        keys = {(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)}
        return d * k - len(keys)

    def evaluate():
        reach = _reach(k, G, D, nbr, d)
        return _unreached(k, N, reach) + _PENALTY * dupcount()

    def restore(snap_layers, snap_S):
        for l in range(d):
            layers[l] = list(snap_layers[l])
            S[l] = list(snap_S[l])
        for l in range(d):
            for i in range(k):
                setd(l, i)

    cur = evaluate()
    best_cost = cur
    best_snap = ([list(x) for x in layers], [list(x) for x in S])
    coords = [(l, i) for l in range(d) for i in range(k)]
    cand_n = min(G, 64)
    stale = 0

    while cur > 0 and time.monotonic() < deadline:
        prev = cur
        rng.shuffle(coords)
        for l, i in coords:
            if time.monotonic() > deadline:
                break
            old = S[l][i]
            bestc, bests = cur, old
            for s in rng.sample(range(G), cand_n):
                if s == old:
                    continue
                S[l][i] = s
                setd(l, i)
                c = evaluate()
                if c < bestc:
                    bestc, bests = c, s
                elif c == bestc and bests == old and rng.random() < 0.2:
                    bests = s  # plateau move
            S[l][i] = bests
            setd(l, i)
            cur = bestc
            if cur == 0:
                break

        if cur < best_cost:
            best_cost = cur
            best_snap = ([list(x) for x in layers], [list(x) for x in S])

        if cur < prev:
            stale = 0
        else:
            stale += 1

        if cur > 0 and stale >= 3:
            # Iterated local search kick: restart from best or perturb current.
            if rng.random() < 0.5:
                restore(*best_snap)
            for _ in range(3):
                l = rng.randrange(d)
                i = rng.randrange(k)
                S[l][i] = rng.randrange(G)
                setd(l, i)
            if k >= 2 and rng.random() < 0.5:
                l = rng.randrange(d)
                i1, i2 = rng.sample(range(k), 2)
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                setd(l, i1)
                setd(l, i2)
            cur = evaluate()
            stale = 0

    if best_cost != 0:
        return None
    restore(*best_snap)
    if evaluate() != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact constructions (fast, safe).
    if D >= 3:
        if 3 <= d - 2 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Goal order: start at a fraction of the Moore bound and climb on success.
    moore = lib.moore_bound(d, D)
    goal = max(best_n + 2, int(0.37 * moore))

    try:
        while time.monotonic() < deadline:
            k = rng.choice([1, 2, 2, 3, 3, 4])
            target_G = -(-goal // (2 * k))
            g = _sample_group(target_G, rng)
            if g is None:
                continue
            m, k2, r = g
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            if 2 * k * G <= best_n:
                continue
            trial_deadline = min(deadline, time.monotonic() + 12.0)
            res = _ils(d, D, k, G, Ts, Invs, rng, trial_deadline)
            if res is not None and res[0] > best_n:
                before = best_n
                consider(res[0], res[1])
                if best_n > before:
                    goal = best_n + 2
                    continue
            goal = max(best_n + 2, int(goal * 0.99))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
