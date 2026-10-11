import itertools
import math
import random
import time

import numpy as np

import lib

T_HOT = 4.0          # initial annealing temperature (unreached-pair units)
T_COLD = 0.2         # final annealing temperature
CYCLE = 2000         # annealing temperature restarts every CYCLE steps
A_CHOICES = (1, 2, 2, 3, 3, 4, 4, 5, 6)   # base-graph sizes per side (lift has 2*a*N vertices)
WINDOW = 3           # group order N is sampled from [lo, lo + WINDOW]
N_CAP = 400          # largest group order we will build tables for
BUDGET_START = 1.5   # seconds per lift attempt
BUDGET_CAP = 5.0
VMAX_CAP = 2500      # never build graphs larger than this


# ----------------------------------------------------------------------------
# Safe baseline families (always validated with lib.is_valid before use).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Generalized voltage lifts over groups Z_m x|_r Z_k.
#
# Base graph: parts A = {0..a-1}, B = {0..a-1}, d-regular bipartite multigraph
# built from d permutations sig[t] of range(a). Dart (t, i) joins A_i to B_{sig[t][i]}
# with voltage gv[t][i] in G. Lift vertices: A_i,x = i*N + x and B_j,y = (a+j)*N + y,
# with edges A_i,x -- B_j,x*g.
#
# Left multiplication by h is an automorphism, so distances from the 2a vertices
# A_i,e and B_j,e determine the diameter. The search is simulated annealing over the
# voltages. Reachability is tracked with one bitmask per vertex, using numpy.
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    if N in _GROUP_CACHE:
        return _GROUP_CACHE[N]
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUP_CACHE[N] = out
    return out


def _table(m, k, r):
    """Return (N, T, invs): T[x, g] = x*g as an array, invs[g] = g^{-1}."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(order)] for x in range(order)], dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    return order, T, invs


def _set_col(nb, a, N, T, invs, t, i, j, g):
    """Write dart (t, i) -> (j, g) into column t of the neighbour table nb."""
    nb[i * N:(i + 1) * N, t] = (a + j) * N + T[:, g]
    nb[(a + j) * N:(a + j + 1) * N, t] = i * N + T[:, invs[g]]


def _lift_cost(nb, V, a, D, src, bits):
    """Number of (source, vertex) pairs not within distance D, over the 2a sources."""
    R = np.zeros(V, dtype=np.int64)
    R[src] = bits
    for _ in range(D):
        R = R | np.bitwise_or.reduce(R[nb], axis=1)
    cnt = 0
    for s in range(len(bits)):
        cnt += int(np.count_nonzero(R & bits[s]))
    return len(bits) * V - cnt


def _anneal_lift(a, N, T, invs, d, D, rng, deadline):
    """Search for voltages giving diameter <= D. Returns (sig, gv) or None."""
    V = 2 * a * N
    sig = [rng.sample(range(a), a) for _ in range(d)]
    gv = [[0] * a for _ in range(d)]
    used = {}
    for t in range(d):
        for i in range(a):
            j = sig[t][i]
            s = used.setdefault((i, j), set())
            choices = [c for c in range(N) if c not in s]
            if not choices:
                return None
            g = rng.choice(choices)
            s.add(g)
            gv[t][i] = g

    nb = np.zeros((V, d), dtype=np.int64)
    for t in range(d):
        for i in range(a):
            _set_col(nb, a, N, T, invs, t, i, sig[t][i], gv[t][i])
    src = np.array([i * N for i in range(a)] + [(a + j) * N for j in range(a)], dtype=np.int64)
    bits = np.array([1 << s for s in range(2 * a)], dtype=np.int64)

    cur = _lift_cost(nb, V, a, D, src, bits)
    it = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        it += 1
        temp = T_HOT * (T_COLD / T_HOT) ** ((it % CYCLE) / CYCLE)
        t = rng.randrange(d)
        i = rng.randrange(a)
        j = sig[t][i]
        g_old = gv[t][i]
        g_new = rng.randrange(N)
        if g_new == g_old:
            continue
        if any(sig[t2][i] == j and gv[t2][i] == g_new for t2 in range(d) if t2 != t):
            continue
        gv[t][i] = g_new
        _set_col(nb, a, N, T, invs, t, i, j, g_new)
        v = _lift_cost(nb, V, a, D, src, bits)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gv[t][i] = g_old
            _set_col(nb, a, N, T, invs, t, i, j, g_old)
    return sig, gv


def _edges_from(a, N, T, sig, gv, d):
    """Expand the base-graph description into the lift's edge list."""
    edges = []
    for t in range(d):
        for i in range(a):
            j = sig[t][i]
            g = gv[t][i]
            col = T[:, g].tolist()
            ba = i * N
            bb = (a + j) * N
            edges.extend((ba + x, bb + col[x]) for x in range(N))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
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

    # Main search: generalized lifts of small bipartite base multigraphs.
    moore = lib.moore_bound(d, D)
    vmax = min(moore, VMAX_CAP)
    budget = BUDGET_START

    while time.monotonic() < deadline and best_n < vmax:
        a = rng.choice(A_CHOICES)
        lo = max(d, -(-(best_n + 1) // (2 * a)))
        hi = min(vmax // (2 * a), lo + WINDOW, N_CAP)
        if hi < lo:
            continue
        N = rng.randint(lo, hi)
        groups = _groups(N)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        order, T, invs = _table(m, k, r)

        att_deadline = min(deadline, time.monotonic() + budget)
        res = _anneal_lift(a, order, T, invs, d, D, rng, att_deadline)
        if res is None:
            budget = min(BUDGET_CAP, budget * 1.05)
            continue
        sig, gv = res
        edges = _edges_from(a, order, T, sig, gv, d)
        consider(2 * a * order, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
