import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact families (used as fallbacks and for calibration-style cases).
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
# A different search paradigm from the parent: bi-Cayley lifts over metacyclic
# groups Z_m x| Z_k2, but the voltages are found by COORDINATE DESCENT
# (best-response on one dart at a time, over sampled voltages) with
# kick-perturbations on stall, instead of simulated annealing from random.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l joins A_i to B_{layers[l][i]} with voltage s: A_{i,g} ~ B_{j, g*s}.
# Every layer is a permutation, so the graph is bipartite and d-regular
# (duplicate edges are merged, which can only lower degree; validity is kept).
# Left multiplication is an automorphism, so the 2k block representatives
# suffice to test the diameter.
# ----------------------------------------------------------------------------

_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (2, 3, 4, 5, 6)
_MAX_G = 420
_TRIAL_SECONDS = 12.0


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target and order <= _MAX_G, or None."""
    k2_choices = [1, 1, 2, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24]
    for _ in range(300):
        k2 = rng.choice(k2_choices)
        m = max(2, -(-target // k2))
        if m * k2 > _MAX_G:
            continue
        if k2 == 1 or rng.random() < 0.3:
            r = 1
        else:
            cands = [c for c in range(1, m)
                     if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
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
    """Write layer l's neighbours for A-block i (joined to B-block j with voltage s), both directions."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr):
    """Bitmask per vertex: bit b set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[0]):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _lift_search(d, D, k, G, Ts, Invs, rng, deadline):
    """Coordinate descent over voltages for a fixed group and fixed layer permutations.

    Returns (n, edges) on success (every pair within distance D), else None.
    """
    N = 2 * k * G
    total = 2 * k * N
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[0] * k for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def forb_full(l, i):
        j = layers[l][i]
        return {S[l2][i] for l2 in range(d) if l2 != l and layers[l2][i] == j}

    def put(l, i):
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def cost():
        return total - int(_POP[_reach(k, G, D, nbr)].sum())

    # Dupe-avoiding initial fill (only against earlier layers).
    for l in range(d):
        for i in range(k):
            j = layers[l][i]
            f = {S[l2][i] for l2 in range(l) if layers[l2][i] == j}
            s = rng.randrange(G)
            for _ in range(50):
                if s not in f:
                    break
                s = rng.randrange(G)
            S[l][i] = s
            put(l, i)

    cur = cost()
    sweeps = 0
    while cur > 0 and time.monotonic() < deadline:
        sweeps += 1
        improved = False
        order = [(l, i) for l in range(d) for i in range(k)]
        rng.shuffle(order)
        for l, i in order:
            if time.monotonic() > deadline:
                break
            f = forb_full(l, i)
            old = S[l][i]
            bc, bs = cur, old
            for s in rng.sample(range(G), min(G, 60)):
                if s == old or s in f:
                    continue
                S[l][i] = s
                put(l, i)
                c = cost()
                if c < bc:
                    bc, bs = c, s
            S[l][i] = bs
            put(l, i)
            if bs != old:
                improved = True
            cur = bc
            if cur == 0:
                break
        if cur > 0 and not improved:
            # Stall: kick a few darts to random dupe-free voltages.
            for _ in range(3):
                l = rng.randrange(d)
                i = rng.randrange(k)
                f = forb_full(l, i)
                s = rng.randrange(G)
                for _ in range(50):
                    if s not in f:
                        break
                    s = rng.randrange(G)
                S[l][i] = s
                put(l, i)
            cur = cost()

    if cur != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (and is optimal for D = 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D <= 2:
        return best

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

    # Main search: many short coordinate-descent trials over varied groups/base sizes.
    if d < 2:
        return best
    while time.monotonic() < deadline - 1.0:
        k = rng.choice(_KS)
        G_min = best_n // (2 * k) + 1
        target = G_min + rng.randrange(0, 1 + G_min // 12)
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        Gord, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * Gord <= best_n or Gord <= d:
            continue
        trial_deadline = min(deadline, time.monotonic() + _TRIAL_SECONDS)
        res = _lift_search(d, D, k, Gord, Ts, Invs, rng, trial_deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
