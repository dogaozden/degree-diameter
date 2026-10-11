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
# Group sampler over EXACT orders (new).
#
# For a target order G we enumerate every factorisation G = m * k2 and every
# action r of Z_k2 on Z_m that lib.semidirect_group accepts. r = 1 gives the
# direct product Z_m x Z_k2, which the parent never sampled. Returning the
# exact order lets the search target G just above the current record.
# ----------------------------------------------------------------------------

def _group_options(G, rng):
    """Return (m, k2, r) triples for groups Z_m x|_r Z_k2 of order exactly G."""
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        rs = {1}  # direct product, always valid
        if m > 2:
            for _ in range(30):
                c = rng.randrange(2, m)
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    rs.add(c)
        for r in rs:
            opts.append((m, k2, r))
    return opts


# ----------------------------------------------------------------------------
# Bitmask ball cost over representatives (new helper).
#
# With a bi-Cayley lift, every vertex class is one orbit under left
# multiplication. So it suffices to check distances from the 2k representatives.
# Each vertex v carries a 64-bit mask: bit t is set when representative t lies
# within the current radius of v. D rounds of OR-propagation over the d-regular
# neighbour table give all the masks. This is vectorised with numpy.
# ----------------------------------------------------------------------------

def _nbrs(k, G, d, layers, P):
    """Neighbour table of shape (2kG, d). Row a lists all neighbours of vertex a."""
    N = 2 * k * G
    nb = np.empty((N, d), dtype=np.int64)
    ar = np.arange(G, dtype=np.int64)
    for l in range(d):
        row = layers[l]
        for i in range(k):
            j = row[i]
            pm = P[l][i]
            nb[i * G:(i + 1) * G, l] = (k + j) * G + pm
            nb[(k + j) * G + pm, l] = i * G + ar
    return nb


def _reach_cost(nb, k, G, D):
    """Number of unreached (representative, vertex) pairs within radius D."""
    N = nb.shape[0]
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    M = np.zeros(N, dtype=np.uint64)
    for t, r in enumerate(reps):
        M[r] = np.uint64(1) << np.uint64(t)
    for _ in range(D):
        M = M | np.bitwise_or.reduce(M[nb], axis=1)
    reached = int(np.unpackbits(M.view(np.uint8)).sum())
    return N * len(reps) - reached


_PENALTY = 1000


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over layer permutations and voltages.

    Layer l sends A_i to B_{layers[l][i]} with voltage S[l][i]. Every vertex
    then has degree d. Returns (n, edges) with diameter <= D, or None.
    """
    N = 2 * k * G
    cache = {}

    def col(s):
        c = cache.get(s)
        if c is None:
            c = np.array([mul(g, s) for g in range(G)], dtype=np.int64)
            cache[s] = c
        return c

    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    P = [[col(S[l][i]) for i in range(k)] for l in range(d)]

    def evaluate():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        dup = len(keys) - len(set(keys))
        nb = _nbrs(k, G, d, layers, P)
        return _reach_cost(nb, k, G, D) + _PENALTY * dup, nb

    cur, nb = evaluate()
    for t in range(iters):
        if cur == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        temp = 3.0 * (1.0 - t / iters) + 0.05

        if k > 1 and rng.random() < 0.2:
            # Swap two target classes inside one layer (new move).
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            new, nnb = evaluate()
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur, nb = new, nnb
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
        else:
            # Change one voltage.
            l = rng.randrange(d)
            i = rng.randrange(k)
            s = rng.randrange(G)
            if s == S[l][i]:
                continue
            old_s, old_p = S[l][i], P[l][i]
            S[l][i] = s
            P[l][i] = col(s)
            new, nnb = evaluate()
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur, nb = new, nnb
            else:
                S[l][i], P[l][i] = old_s, old_p

    if cur == 0:
        edges = set()
        for a in range(k * G):
            for b in nb[a]:
                edges.add((a, int(b)))
        return N, sorted(edges)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # d = 2: the cycle C_{2D} is an exact optimum.
    if d == 2:
        consider(*lib.haar_graph(D, [0, 1]))
        return best

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

    # Main search: bi-Cayley lifts over exact-order groups, including direct products.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 2, 2, 3, 4])
        base = best_n // (2 * k)
        span = max(2, base // 8)
        G = max(2, base + 1 + rng.randrange(span))
        opts = _group_options(G, rng)
        if not opts:
            continue
        m, k2, r = rng.choice(opts)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        res = _anneal(d, D, k, order, mul, rng, deadline, 5000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
