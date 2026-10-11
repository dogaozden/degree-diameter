import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact families (kept from the parent for calibration cases).
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
# NEW construction: affine-permutation bi-lifts over Z_p (p prime).
#
# Vertices: A_{i,x} = i*p + x,  B_{j,y} = (k+j)*p + y, for blocks i, j < k.
# Each layer l is a bijection layers[l] from A-blocks to B-blocks.
# The dart of layer l at A-block i is the affine map P = (a, b):
#     A_{i,x} ~ B_{j,(a x + b) mod p},  j = layers[l][i],  a in Z_p^*.
# Every vertex has exactly one neighbour per layer, so the degree is d.
#
# Unlike the parent's group lifts, these are permutation voltages (AGL(1,p)),
# and vertices are not assumed transitive. Diameter is checked for ALL sources
# with packed bitsets in numpy, and annealing minimises the number of
# unreachable ordered pairs.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)
_DUP_PEN_FACTOR = 4


def _is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    f = 3
    while f * f <= n:
        if n % f == 0:
            return False
        f += 2
    return True


def _next_prime(x):
    while not _is_prime(x):
        x += 1
    return x


def _build_nbr(k, p, d, layers, P):
    """Return the (d, N) neighbour table for the affine bi-lift."""
    N = 2 * k * p
    nbr = np.empty((d, N), dtype=np.int64)
    ar = np.arange(p, dtype=np.int64)
    for l in range(d):
        for i in range(k):
            j = layers[l][i]
            a, b = P[l][i]
            y = (a * ar + b) % p
            nbr[l, i * p:(i + 1) * p] = (k + j) * p + y
            ainv = pow(a, -1, p)
            x = (ainv * (ar - b)) % p  # x with a*x + b = y, indexed by y
            nbr[l, (k + j) * p:(k + j + 1) * p] = i * p + x
    return N, nbr


def _unreached(N, nbr, d, D, eye_packed):
    """Number of ordered (source, target) pairs at distance > D."""
    reach = eye_packed
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return N * N - int(_POP8[reach].sum())


def _anneal(d, D, k, p, rng, deadline, iters):
    """Annealing over affine darts and layer swaps. Returns (N, nbr) on success, else None."""
    N = 2 * k * p
    eye_packed = np.packbits(np.eye(N, dtype=bool), axis=1)
    pen = _DUP_PEN_FACTOR * p

    layers = [rng.sample(range(k), k) for _ in range(d)]
    P = [[(rng.randrange(1, p), rng.randrange(p)) for _ in range(k)] for _ in range(d)]

    def evaluate(layers, P):
        _, nbr = _build_nbr(k, p, d, layers, P)
        keys = [(i, layers[l][i], P[l][i]) for l in range(d) for i in range(k)]
        dup = len(keys) - len(set(keys))
        return _unreached(N, nbr, d, D, eye_packed) + pen * dup, nbr

    cur, cur_nbr = evaluate(layers, P)
    c0 = float(max(cur, 1))
    T0 = max(1.0, 0.02 * c0)

    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, T0 * (0.01 ** (t / iters)))

        if k >= 2 and rng.random() < 0.2:
            # Layer swap: exchange the B-targets of two A-blocks in one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            c2, nb2 = evaluate(layers, P)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
                cur, cur_nbr = c2, nb2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            continue

        l = rng.randrange(d)
        i = rng.randrange(k)
        old = P[l][i]
        r = rng.random()
        if r < 0.4:
            new = (rng.randrange(1, p), old[1])
        elif r < 0.8:
            new = (old[0], rng.randrange(p))
        else:
            new = (rng.randrange(1, p), rng.randrange(p))
        if new == old:
            continue
        P[l][i] = new
        c2, nb2 = evaluate(layers, P)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur, cur_nbr = c2, nb2
        else:
            P[l][i] = old

    if cur != 0:
        return None
    edges = set()
    for u in range(k * p):
        for l in range(d):
            edges.add((u, int(cur_nbr[l, u])))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
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

    if D == 2:
        return best

    # Exact constructions for calibration-style cases.
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

    # Main search: affine bi-lifts with a bandit over the number of blocks k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    chunk = max(3.0, min(15.0, budget / 4.0))
    while time.monotonic() < deadline:
        k = pick_k()
        pmin = max(2, best_n // (2 * k) + 1)  # guarantees 2*k*p > best_n
        p = _next_prime(pmin + rng.randrange(0, 4))
        chunk_deadline = min(deadline, time.monotonic() + chunk)
        trials[k] += 1
        res = _anneal(d, D, k, p, rng, chunk_deadline, 6000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
