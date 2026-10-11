import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact fallback families (unchanged from the parent; used for small or
# calibration cases and as the safe baseline).
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
# Different search: steepest-descent coordinate search over bi-Cayley lifts.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Each layer is a permutation, so the graph is d-regular and bipartite.
#
# Instead of simulated annealing, each pass re-optimises every single dart
# (layer l, block i) over a candidate set of voltages and keeps the best one.
# When a pass stalls, one whole layer is re-randomised (iterated local search).
# Left multiplication is an automorphism, so only the 2k block representatives
# need to be checked for distance <= D.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target."""
    k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 10, 12])
    m = max(2, -(-target // k2)) + rng.randrange(0, 3)
    if k2 == 1:
        return m, 1, 1
    r = None
    if k2 == 2 and rng.random() < 0.3:
        c = m - 1
        if m > 2 and math.gcd(c, m) == 1 and pow(c, 2, m) == 1 % m:
            r = c
    if r is None:
        for _ in range(80):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    if r is None:
        r = 1  # direct product Z_m x Z_k2, always a valid group
    return m, k2, r


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
    """Write layer l's neighbours for A-block i and B-block j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline):
    """Steepest-descent dart re-optimisation with layer kicks. Returns (n, edges) or None."""
    N = 2 * k * G
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def setl(l, i):
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    for l in range(d):
        for i in range(k):
            setl(l, i)

    def evaluate():
        reach = _reach(k, G, D, nbr, d)
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        dup = len(keys) - len(set(keys))
        return _unreached(k, N, reach) + _PENALTY * dup

    cost = evaluate()
    while cost > 0 and time.monotonic() < deadline:
        improved = False
        order = [(l, i) for l in range(d) for i in range(k)]
        rng.shuffle(order)
        for l, i in order:
            if cost == 0 or time.monotonic() > deadline:
                break
            old = S[l][i]
            cands = range(G) if G <= 160 else rng.sample(range(G), 160)
            bestc, bests = cost, old
            for s in cands:
                if s == old:
                    continue
                S[l][i] = s
                setl(l, i)
                c = evaluate()
                if c < bestc:
                    bestc, bests = c, s
            S[l][i] = bests
            setl(l, i)
            if bests != old:
                improved = True
            cost = bestc
        if cost > 0 and not improved and time.monotonic() < deadline:
            # Iterated local search: re-randomise one whole layer.
            l = rng.randrange(d)
            layers[l] = rng.sample(range(k), k)
            S[l] = [rng.randrange(G) for _ in range(k)]
            for i in range(k):
                setl(l, i)
            cost = evaluate()

    if cost != 0:
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

    # Main search: random base size k, group near the needed order, steepest descent.
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        k = rng.randint(1, 6)
        target = max(2, best_n // (2 * k) + 1 + rng.randrange(0, max(2, best_n // (20 * k) + 2)))
        m, k2, r = _sample_group(target, rng)
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        slice_end = time.monotonic() + min(remaining, 10.0)
        res = _search(d, D, k, G, Ts, Invs, rng, min(slice_end, deadline))
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
