import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline families (fast, always valid, used as the safe floor).
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
# A different family from the previous parent: bi-Cayley lifts over
# NON-CYCLIC groups. Both abelian Z_a x Z_b (non-cyclic when gcd(a,b) > 1) and
# semidirect products Z_m x| Z_k2 are tried. Groups are given by a full
# multiplication table, so voltage changes are cheap column lookups.
#
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h, identity = element 0.
# Layer l with base vertex i and voltage s joins A_{i,g} to B_{p_l(i), g*s}.
# Each layer is a permutation of the base, so every vertex has degree d.
# Left multiplication is an automorphism, so only the 2k representatives
# need BFS; reachability is tracked as numpy bitmasks.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_MAX_ORDER = 1600


def _sample_group(target, rng):
    """Return ("ab", (a, b)) or ("sd", (m, k2, r)) for a group of order >= target, or None."""
    for _ in range(300):
        if rng.random() < 0.4:
            a = rng.randint(2, 40)
            b = -(-target // a)
            if b >= 2:
                return ("ab", (a, b))
            continue
        k2 = rng.choice([2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24])
        m = -(-target // k2)
        if m < 2:
            continue
        r = None
        for _ in range(80):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
        if r is None:
            continue
        return ("sd", (m, k2, r))
    return None


def _group_table(kind, params):
    """Return (order, table) with table[x, y] = x*y and identity 0."""
    if kind == "ab":
        a, b = params
        order = a * b
        x = np.arange(order, dtype=np.int64)
        x1, y1 = (x // b)[:, None], (x % b)[:, None]
        x2, y2 = (x // b)[None, :], (x % b)[None, :]
        table = ((x1 + x2) % a) * b + (y1 + y2) % b
    else:
        m, k2, r = params
        order = m * k2
        pw = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
        x = np.arange(order, dtype=np.int64)
        a1, b1 = (x // k2)[:, None], (x % k2)[:, None]
        a2, b2 = (x // k2)[None, :], (x % k2)[None, :]
        table = ((a1 + pw[b1] * a2) % m) * k2 + (b1 + b2) % k2
    return order, table.astype(np.int64)


def _search(d, D, k, G, table, rng, deadline, iters):
    """Simulated annealing over voltages for a base with k vertices per side.

    Returns (n, edges) with diameter <= D, or None.
    """
    N = 2 * k * G
    ar = np.arange(G, dtype=np.int64)
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nb = np.zeros((N, d), dtype=np.int64)

    def assign(l, i, s):
        j = layers[l][i]
        pm = table[:, s]
        nb[i * G:(i + 1) * G, l] = (k + j) * G + pm
        inv = np.empty(G, dtype=np.int64)
        inv[pm] = ar
        nb[(k + j) * G:(k + j + 1) * G, l] = i * G + inv

    for l in range(d):
        for i in range(k):
            assign(l, i, S[l][i])

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

    # Main search over non-cyclic / semidirect bi-Cayley lifts.
    try:
        while time.monotonic() < deadline:
            k = rng.choice([1, 1, 2, 2, 3, 4])
            need = best_n // (2 * k) + 1          # group order giving N > best_n
            target = need + rng.randrange(0, max(2, need // 20 + 1))
            if target > _MAX_ORDER:
                target = max(2, need)
            if target > _MAX_ORDER:
                continue
            g = _sample_group(target, rng)
            if g is None:
                continue
            G, table = _group_table(*g)
            if G > _MAX_ORDER or 2 * k * G <= best_n:
                continue
            res = _search(d, D, k, G, table, rng, deadline, 12000)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
