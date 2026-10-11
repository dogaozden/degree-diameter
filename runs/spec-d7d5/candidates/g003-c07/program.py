import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline families (kept as safe, instant answers where they apply).
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
# Bi-Cayley lifts over non-abelian groups, found by annealing.
#
# Vertex blocks: A-block i (i < k) is vertices i*G .. i*G+G-1, B-block j is
# (k+j)*G .. (k+j)*G+G-1. Element g of block b is b*G + g.
# Layer l pairs A-block i with B-block layers[l][i] through voltage S[l][i]:
#     A_{i,g} ~ B_{layers[l][i], g*s}.
# Each layer is a perfect matching between blocks, so the graph is d-regular
# and bipartite. Left multiplication is an automorphism, so the 2k vertices
# g = identity (one per block) represent all vertex orbits; reachability is
# tracked with bitmasks, one bit per representative.
# ----------------------------------------------------------------------------

_PENALTY = 1000


def _make_group(G, rng):
    """Return (order, mul, inv) for a non-abelian group of order near G, or None.

    Mixes dihedral groups Z_m x| Z_2 (r = -1) with random semidirect products Z_m x| Z_k2.
    """
    for _ in range(100):
        if rng.random() < 0.6:
            m = max(3, G // 2)
            try:
                return lib.semidirect_group(m, 2, m - 1)
            except ValueError:
                continue
        k2 = rng.choice([2, 3, 4, 5, 6, 7, 8, 9, 10, 12])
        m = max(2, G // k2)
        if m < 3:
            continue
        r = None
        for _ in range(80):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
        if r is None:
            continue
        try:
            return lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
    return None


def _table_and_inv(order, mul, inv):
    """Precompute the full multiplication table and inverse array of a group."""
    MT = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        MT[x] = [mul(x, y) for y in range(order)]
    INV = np.array([inv(x) for x in range(order)], dtype=np.int64)
    return MT, INV


def _anneal(d, D, k, G, MT, INV, rng, deadline, iters):
    """Simulated annealing over voltages of a bi-Cayley base with k vertices per side.

    Returns (n, edges) with diameter <= D and max degree d, or None.
    """
    N = 2 * k * G
    nreps = 2 * k
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nb = np.zeros((N, d), dtype=np.int64)

    def assign(l, i, s):
        """Write dart (l, i) with voltage s into the neighbour column l of both blocks."""
        j = layers[l][i]
        # A_{i,g} -> B_{j, g*s}
        nb[i * G:(i + 1) * G, l] = (k + j) * G + MT[:, s]
        # B_{j,h} -> A_{i, h*s^-1}
        nb[(k + j) * G:(k + j + 1) * G, l] = i * G + MT[:, INV[s]]

    for l in range(d):
        for i in range(k):
            assign(l, i, S[l][i])

    base = np.zeros(N, dtype=np.int64)
    for r in range(nreps):
        base[r * G] = 1 << r  # identity element of block r

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
        i = rng.randrange(k)
        old_s = S[l][i]
        new_s = rng.randrange(G)
        assign(l, i, new_s)
        S[l][i] = new_s
        c2 = cost()
        temp = 2.0 * (1.0 - t / iters) + 0.05
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            assign(l, i, old_s)
            S[l][i] = old_s

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

    if D == 2:
        return best

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid. Returns True if adopted."""
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

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

    # Main search: bi-Cayley lifts over non-abelian groups.
    # The target order ratchets up with every success.
    try:
        if d >= 2:
            while time.monotonic() < deadline:
                k = rng.choice([1, 1, 1, 2, 2, 3])
                want = best_n + max(2, best_n // 60)
                G = -(-want // (2 * k)) + rng.randrange(0, 3)
                grp = _make_group(G, rng)
                if grp is None:
                    continue
                order, mul, inv = grp
                if order > 1200 or 2 * k * order <= best_n:
                    continue
                MT, INV = _table_and_inv(order, mul, inv)
                for _ in range(2):
                    if time.monotonic() >= deadline:
                        break
                    res = _anneal(d, D, k, order, MT, INV, rng, deadline, 3000)
                    if res is not None and consider(res[0], res[1]):
                        break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
