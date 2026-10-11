import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline families.
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
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h.
# Layer l is a permutation layers[l] of range(k): A_{i,g} is joined to
# B_{layers[l][i], g*S[l][i]}. Every vertex then has degree d.
#
# Search moves (new in this version):
#   * voltage reassignment in one layer,
#   * swapping the B-targets of two base vertices inside a layer,
#   * swapping the voltages of two base vertices inside a layer.
# Each move rebuilds only one layer's columns of the neighbour table, and an
# undo restores that layer. Voltage permutation tables are cached per group.
# Reachability is tracked with numpy bitmasks, one bit per representative.
# ----------------------------------------------------------------------------

_PENALTY = 1000


def _sample_group(target, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order near target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
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
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over layer permutations and voltages of a base with k vertices per side.

    Returns (n, edges) with diameter <= D, or None.
    """
    N = 2 * k * G
    ar = np.arange(G, dtype=np.int64)
    cache = {}

    def pmap(s):
        """Permutation g -> g*s of the group, as an array (cached per voltage)."""
        arr = cache.get(s)
        if arr is None:
            arr = np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)
            cache[s] = arr
        return arr

    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nb = np.zeros((N, d), dtype=np.int64)

    def assign(l, i, s):
        """Write dart (l, i) with voltage s into column l of the neighbour table, both sides."""
        j = layers[l][i]
        pm = pmap(s)
        nb[i * G:(i + 1) * G, l] = (k + j) * G + pm
        inv = np.empty(G, dtype=np.int64)
        inv[pm] = ar
        nb[(k + j) * G:(k + j + 1) * G, l] = i * G + inv

    def rebuild(l):
        """Rewrite column l of the neighbour table from the current layer l."""
        for i in range(k):
            assign(l, i, S[l][i])

    for l in range(d):
        rebuild(l)

    base = np.zeros(N, dtype=np.int64)
    for r in range(k):
        base[r * G] = 1 << r
    for j in range(k):
        base[(k + j) * G] = 1 << (k + j)
    nreps = 2 * k

    def dup_count():
        seen = set()
        dup = 0
        for l in range(d):
            for i in range(k):
                key = (i, layers[l][i], S[l][i])
                if key in seen:
                    dup += 1
                else:
                    seen.add(key)
        return dup

    def cost():
        reach = base
        for _ in range(D):
            reach = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        reached = 0
        for r in range(nreps):
            reached += int(np.count_nonzero(reach & (1 << r)))
        return N * nreps - reached + _PENALTY * dup_count()

    cur = cost()
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        old_perm = list(layers[l])
        old_S = list(S[l])
        mv = rng.random()
        if mv < 0.4 or k == 1:
            # Reassign one voltage.
            i = rng.randrange(k)
            S[l][i] = rng.randrange(G)
        elif mv < 0.7:
            # Swap the B-targets of two base vertices in this layer.
            a, b = rng.sample(range(k), 2)
            layers[l][a], layers[l][b] = layers[l][b], layers[l][a]
        else:
            # Swap the voltages of two base vertices in this layer.
            a, b = rng.sample(range(k), 2)
            S[l][a], S[l][b] = S[l][b], S[l][a]
        rebuild(l)
        c2 = cost()
        temp = 2.0 * (1.0 - t / iters) + 0.05
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            layers[l] = old_perm
            S[l] = old_S
            rebuild(l)

    if cur != 0:
        return None
    E = set()
    for x in range(N):
        for y in nb[x].tolist():
            if x != y:
                E.add((x, y) if x < y else (y, x))
    return N, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
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

    # Exact constructions: return immediately for calibration-style cases.
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

    # Main search: bi-Cayley lifts over semidirect products with 1-4 base vertices per side.
    try:
        while time.monotonic() < deadline:
            k = rng.choice([1, 2, 2, 3, 3, 4])
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            order, mul = g
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            res = _anneal(d, D, k, order, mul, rng, deadline, 6000)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
