import itertools
import math
import random
import time

import numpy as np

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Safe fallback and cheap algebraic baselines.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """K_{d,d} (diameter 2) for D >= 2; K_2 for D == 1; a single vertex otherwise."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (diameter 3)."""
    for q in range(min(d - 1, 31), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q) (diameter 4)."""
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, searched with
# a numpy-vectorised reachability cost (reps suffice by left-translation symmetry).
#
# Base: k vertices per side, d layers. Layer L is a permutation p_L of range(k)
# together with voltages volt[L][i]. Dart (i, p_L(i), s) joins A_{i,g} to
# B_{p_L(i), g*s} for every group element g.
# ----------------------------------------------------------------------------

def _sample_group(G, rng, k2_choices):
    """Return (order, mul, inv) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice(k2_choices)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 80))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            return lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
    return None


class _Lift:
    def __init__(self, k, G, d, mul, inv):
        self.k, self.G, self.d = k, G, d
        self.N = 2 * k * G
        self.mul, self.inv = mul, inv
        self.cache = {}

    def perms(self, s):
        c = self.cache.get(s)
        if c is None:
            G, mul = self.G, self.mul
            si = self.inv(s)
            pm = np.array([mul(g, s) for g in range(G)], dtype=np.int64)
            pmi = np.array([mul(h, si) for h in range(G)], dtype=np.int64)
            c = (pm, pmi)
            self.cache[s] = c
        return c

    def nbrs(self, p, volt):
        """Neighbour table of shape (N, d); column L is the neighbour through layer L."""
        k, G, d = self.k, self.G, self.d
        nb = np.empty((self.N, d), dtype=np.int64)
        for L in range(d):
            pl, vl = p[L], volt[L]
            for i in range(k):
                j = pl[i]
                pm, pmi = self.perms(vl[i])
                nb[i * G:(i + 1) * G, L] = (k + j) * G + pm
                nb[(k + j) * G:(k + j + 1) * G, L] = i * G + pmi
        return nb

    def darts_ok(self, p, volt):
        seen = set()
        for L in range(self.d):
            for i in range(self.k):
                key = (i, p[L][i], volt[L][i])
                if key in seen:
                    return False
                seen.add(key)
        return True


def _cost(nb, reps, N, D):
    """Number of (representative, vertex) pairs not reached within distance D."""
    S = len(reps)
    R = np.zeros((S, N), dtype=bool)
    R[np.arange(S), reps] = True
    for _ in range(D):
        R = R | R[:, nb].any(axis=2)
    return S * N - int(np.count_nonzero(R))


def _anneal(lift, D, rng, deadline, max_iters):
    """Simulated annealing over voltages and layer permutations. Returns (cost, nb, p, volt) or None."""
    k, d, G = lift.k, lift.d, lift.G
    reps = np.array([i * G for i in range(k)] + [(k + j) * G for j in range(k)], dtype=np.int64)

    p = volt = None
    for _ in range(200):
        p = [rng.sample(range(k), k) for _ in range(d)]
        volt = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
        if lift.darts_ok(p, volt):
            break
    else:
        return None

    def evaluate(p, volt):
        if not lift.darts_ok(p, volt):
            return _BIG, None
        nb = lift.nbrs(p, volt)
        return _cost(nb, reps, lift.N, D), nb

    cost, nb = evaluate(p, volt)
    T = 1.0
    it = 0
    while cost > 0 and it < max_iters and time.monotonic() < deadline:
        it += 1
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.5:
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volt[L][i] = new
            c2, nb2 = evaluate(p, volt)
            if c2 <= limit:
                cost, nb = c2, nb2
            else:
                volt[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            p[L][a], p[L][b] = p[L][b], p[L][a]
            c2, nb2 = evaluate(p, volt)
            if c2 <= limit:
                cost, nb = c2, nb2
            else:
                p[L][a], p[L][b] = p[L][b], p[L][a]
    return cost, nb, p, volt


def _edges_from_nb(nb, k, G):
    """Edge list from the neighbour table; A vertices are 0..kG-1, B vertices follow."""
    N = nb.shape[0]
    d = nb.shape[1]
    rows = np.repeat(np.arange(k * G), d)
    cols = nb[:k * G].ravel()
    return N, [(int(a), int(b)) for a, b in zip(rows, cols)]


# ----------------------------------------------------------------------------
# Diameter repair by vertex deletion (dense numpy reachability).
# ----------------------------------------------------------------------------

def _all_bad(n, E, D):
    """Per-vertex count of vertices at distance more than D."""
    A = np.zeros((n, n), dtype=np.float32)
    if E:
        us = np.array([u for u, _ in E], dtype=np.int64)
        vs = np.array([v for _, v in E], dtype=np.int64)
        A[us, vs] = 1.0
        A[vs, us] = 1.0
    R = np.eye(n, dtype=np.float32)
    for _ in range(D):
        R = np.minimum(np.float32(1.0), R + A @ R)
    return n - np.rint(R.sum(axis=1)).astype(np.int64)


def _repair(n, E, D, deadline, rng, need_n):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_E = n, E
    while time.monotonic() < deadline and cur_n >= need_n:
        bad = _all_bad(cur_n, cur_E, D)
        if bad.max() == 0:
            return cur_n, cur_E
        cand = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(cand)
        cand.sort(key=lambda v: -int(bad[v]))
        batch = max(1, len(cand) // 12)
        dead = set(cand[:batch])
        keep = [v for v in range(cur_n) if v not in dead]
        new = {v: i for i, v in enumerate(keep)}
        cur_E = [(new[u], new[v]) for u, v in cur_E if u in new and v in new]
        cur_n = len(keep)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    best = _fallback(d, D)
    if d < 1 or D < 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    # Cheap algebraic baselines.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Lift search: the main budget goes here.
    k2_pool = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    ks = [1, 1, 1, 2, 2, 3] if D >= 3 else [1, 2]

    while time.monotonic() < deadline - 0.5 and best[0] < moore:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(4, lo // 6)
        G = rng.randint(lo, hi)
        if G < d:
            continue
        g = _sample_group(G, rng, k2_pool)
        if g is None:
            continue
        order, mul, inv = g
        lift = _Lift(k, order, d, mul, inv)

        now = time.monotonic()
        slice_end = min(deadline - 0.5, now + max(2.0, (deadline - now) / 6.0))
        res = _anneal(lift, D, rng, slice_end, 10 ** 9)
        if res is None:
            continue
        cost, nb, p, volt = res

        if cost == 0:
            n, E = _edges_from_nb(nb, k, order)
            consider(n, E)
            continue

        # Near miss: try to repair the oversized lift by deleting far-off vertices.
        if cost <= 60 and lift.N > best[0]:
            rep_end = min(deadline - 0.5, time.monotonic() + 5.0)
            if rep_end > time.monotonic():
                n, E = _edges_from_nb(nb, k, order)
                out = _repair(n, E, D, rep_end, rng, best[0] + 1)
                if out is not None:
                    consider(out[0], out[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
