import itertools
import math
import random
import time

import numpy as np

import lib

# Voltage-lift search over Z_m x| Z_k with a bipartite base multigraph.
# A d-regular bipartite base on b+b vertices is a union of d permutations
# sig[k] (A_i -> B_{sig[k,i]}) with a group voltage volt[k,i] on each dart.
# The lift has 2*b*N vertices. Left multiplication is an automorphism, so
# eccentricities only need the b+b fibre representatives, and the diameter
# test is a multi-source bitset BFS done with numpy.

ITERS = 2500          # annealing steps per restart
MAX_B = 6             # max base vertices per side
W0 = 4                # initial window width (in steps of 2 vertices)
BUDGET0 = 2.5         # seconds per (V) attempt initially
BUDGET_CAP = 8.0      # max seconds per (V) attempt

_GROUP_CACHE = {}
_POP_CACHE = {}


# ----------------------------------------------------------------------------
# Baseline families (always validated before use).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group helpers.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(N, m, k, r):
    """Cached multiplication table M[x, g] = x*g and inverse vector for the group."""
    key = (m, k, r)
    if key not in _GROUP_CACHE:
        if len(_GROUP_CACHE) > 64:
            _GROUP_CACHE.clear()
        _, mul, inv = lib.semidirect_group(m, k, r)
        M = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
        invs = np.array([inv(g) for g in range(N)], dtype=np.int64)
        _GROUP_CACHE[key] = (M, invs)
    return _GROUP_CACHE[key]


def _pop_table(bits):
    if bits not in _POP_CACHE:
        _POP_CACHE[bits] = np.array([bin(i).count("1") for i in range(1 << bits)], dtype=np.int64)
    return _POP_CACHE[bits]


# ----------------------------------------------------------------------------
# Lift adjacency and cost.
# ----------------------------------------------------------------------------

def _nbr(sig, volt, N, b, d, M, invs):
    """Neighbour table (2bN, d). A vertices are i*N+x (i < b); B vertices are bN + j*N + y."""
    Mcol = M[:, volt]                                   # (N, d, b): x*volt[k,i]
    Bidx = sig[None, :, :] * N + Mcol                   # (N, d, b)
    A = np.transpose(Bidx, (2, 0, 1)).reshape(b * N, d) + b * N
    inv_sig = np.argsort(sig, axis=1)                   # inv_sig[k, j] = i with sig[k,i] = j
    Gj = np.take_along_axis(invs[volt], inv_sig, axis=1)  # inverse voltage on dart into B_j
    Aidx = inv_sig[None, :, :] * N + M[:, Gj]           # (N, d, b): y*g^-1 on A side
    Bn = np.transpose(Aidx, (2, 0, 1)).reshape(b * N, d)
    return np.vstack([A, Bn])


def _cost(nb, V, src, bits, pop, D):
    """Number of (fibre representative, vertex) pairs not within distance D."""
    reach = np.zeros(V, dtype=np.int64)
    reach[src] = bits
    for _ in range(D):
        reach = reach | np.bitwise_or.reduce(reach[nb], axis=1)
    return len(src) * V - int(pop[reach].sum())


def _anneal(ctx, sig, volt, rng, stop):
    N, b, d, M, invs, V, src, bits, pop, D = ctx
    nb = _nbr(sig, volt, N, b, d, M, invs)
    cur = _cost(nb, V, src, bits, pop, D)
    T_hot = max(1.0, 0.02 * V)
    T_cold = 0.2
    for it in range(ITERS):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > stop:
            break
        temp = T_hot * (T_cold / T_hot) ** (it / ITERS)
        s2 = sig.copy()
        v2 = volt.copy()
        k = rng.randrange(d)
        if b > 1 and rng.random() < 0.25:
            i, i2 = rng.sample(range(b), 2)
            s2[k, i], s2[k, i2] = s2[k, i2], s2[k, i]
        else:
            v2[k, rng.randrange(b)] = rng.randrange(N)
        nb2 = _nbr(s2, v2, N, b, d, M, invs)
        new = _cost(nb2, V, src, bits, pop, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            sig, volt, cur, nb = s2, v2, new, nb2
    return sig, volt, cur, nb


def _search_V(V, d, D, rng, deadline, budget):
    """Try to find a voltage lift on V vertices with diameter <= D. Returns neighbour table or None."""
    opts = [b for b in range(1, MAX_B + 1) if V % (2 * b) == 0 and V // (2 * b) >= 2]
    if not opts:
        return None
    b = rng.choice(opts)
    N = V // (2 * b)
    groups = _groups(N)
    if not groups:
        return None
    src = np.array([i * N for i in range(b)] + [b * N + j * N for j in range(b)], dtype=np.int64)
    bits = np.array([1 << s for s in range(2 * b)], dtype=np.int64)
    pop = _pop_table(2 * b)
    stop = min(deadline, time.monotonic() + budget)
    while time.monotonic() < stop:
        m, k, r = rng.choice(groups)
        M, invs = _tables(N, m, k, r)
        sig = np.array([rng.sample(range(b), b) for _ in range(d)], dtype=np.int64)
        volt = np.array([[rng.randrange(N) for _ in range(b)] for _ in range(d)], dtype=np.int64)
        ctx = (N, b, d, M, invs, V, src, bits, pop, D)
        sig, volt, cur, nb = _anneal(ctx, sig, volt, rng, stop)
        if cur == 0:
            return nb, V, b, N
    return None


def _edges(nb, bN):
    """Simple edge list from the A-side rows of the neighbour table."""
    es = set()
    for u, row in enumerate(nb[:bN].tolist()):
        for v in row:
            es.add((u, v))
    return list(es)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Safe baselines.
    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Vmax = lib.moore_bound(d, D)

    def even_ge(x):
        return x + (x & 1)

    W = W0
    budget = BUDGET0
    fails = 0
    lo = even_ge(max(best[0] + 1, Vmax // 2))

    while time.monotonic() < deadline:
        lo = max(lo, even_ge(best[0] + 1))
        if lo > Vmax:
            break
        hi = min(Vmax, lo + 2 * W)
        choices = list(range(lo, hi + 1, 2))
        if not choices:
            break
        # Bias toward the low end of the window: easier targets succeed more often.
        V = choices[int(len(choices) * rng.random() ** 2)]
        res = _search_V(V, d, D, rng, deadline, budget)
        if res is not None:
            nb, V2, b, N = res
            consider(V2, _edges(nb, b * N))
            fails = 0
            lo = V2 + 2
        else:
            fails += 1
            if fails % 3 == 0:
                if budget < BUDGET_CAP:
                    budget = min(BUDGET_CAP, budget * 1.5)
                else:
                    lo = max(even_ge(best[0] + 1), lo - 2 * W)

    return best
