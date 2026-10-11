import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Algebraic families (D = 3, D = 4): projective plane, Araujo-Pardo-Lopez,
# and the generalized quadrangle W(q).
# ----------------------------------------------------------------------------

def _pg_candidates(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return [lib.projective_plane_incidence(q)]
    return []


def _araujo_candidates(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return [lib.araujo_lopez_graph(q)]
        except Exception:
            return []
    return []


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


def _gq_candidates(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return [_gq_w(q)]
    return []


# ----------------------------------------------------------------------------
# New family for D >= 5: bi-Cayley lifts over semidirect products Z_m x| Z_k2,
# searched by simulated annealing with a numpy distance-reach cost.
#
# Layout: A-vertex i*G+g and B-vertex (k+j)*G+h. Each of the d layers L holds
# one permutation dj[L] (A-index i -> B-index dj[L][i]) and voltages ds[L][i].
# Edge: A(i,g) -- B(dj, MT[g, ds]). Left translations are automorphisms, so
# only the 2k representatives need to reach every vertex within D.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    divs = [k2 for k2 in range(1, min(G, 12) + 1) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return None
    for _ in range(40):
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            if m < 3:
                continue
            r = rng.randrange(2, m)
            if math.gcd(r, m) != 1 or pow(r, k2, m) != 1 % m:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _anneal_lift(d, D, k, G, MT, rng, end):
    """Anneal voltages and layer permutations until every representative reaches all within D."""
    NA = k * G
    N = 2 * NA
    gidx = np.arange(G, dtype=np.int64)
    Arow3 = np.arange(k, dtype=np.int64)[None, :, None] * G + gidx[None, None, :]
    reps = np.array([i * G for i in range(k)] + [(k + j) * G for j in range(k)], dtype=np.int64)
    cols = np.arange(2 * k)

    dj = np.array([rng.sample(range(k), k) for _ in range(d)], dtype=np.int64)
    ds = np.array([[rng.randrange(G) for _ in range(k)] for _ in range(d)], dtype=np.int64)

    def build_nb(dj, ds):
        Bv = ((k + dj)[:, :, None] * G + MT[gidx[None, None, :], ds[:, :, None]]).ravel()
        A = np.broadcast_to(Arow3, (d, k, G)).ravel()
        oa = np.argsort(A, kind="stable")
        nbA = Bv[oa].reshape(NA, d)
        ob = np.argsort(Bv, kind="stable")
        nbB = A[ob].reshape(NA, d)
        return np.vstack([nbA, nbB])

    def cost(nb):
        R = np.zeros((N, 2 * k), dtype=bool)
        R[reps, cols] = True
        for _ in range(D):
            R = R | R[nb].any(axis=1)
        return N * 2 * k - int(R.sum())

    cur = cost(build_nb(dj, ds))
    it = 0
    while cur > 0 and time.monotonic() < end:
        it += 1
        T = max(0.2, 2.0 * (0.9995 ** it))
        if rng.random() < 0.6 or k == 1:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = int(ds[L, i])
            new = rng.randrange(G)
            if new == old:
                continue
            ds[L, i] = new
            c2 = cost(build_nb(dj, ds))
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                ds[L, i] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            dj[L, a], dj[L, b] = dj[L, b], dj[L, a]
            c2 = cost(build_nb(dj, ds))
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                dj[L, a], dj[L, b] = dj[L, b], dj[L, a]

    if cur != 0:
        return None
    nb = build_nb(dj, ds)
    E = sorted({(a, int(b)) for a in range(NA) for b in nb[a]})
    return N, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(fb_n, fb_e, d, D):
        return 1, []
    best = [fb_n, fb_e]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    if D == 2:
        return best[0], best[1]

    if D >= 3:
        try:
            for n, e in _pg_candidates(d) + _araujo_candidates(d):
                consider(n, e)
        except Exception:
            pass

    if D >= 4:
        try:
            for n, e in _gq_candidates(d):
                consider(n, e)
        except Exception:
            pass

    # Bold new search for D >= 5: bi-Cayley lifts with annealing.
    if D >= 5:
        ks = [1, 2, 3, 4, 6]
        try:
            while time.monotonic() < deadline - 0.5:
                k = rng.choice(ks)
                base = best[0] // (2 * k)
                lo = max(2, base + 1)
                hi = lo + max(2, base // 5)
                G = rng.randint(lo, hi)
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                MT = np.array([[mul(x, y) for y in range(order)] for x in range(order)],
                              dtype=np.int64)
                end = min(deadline, time.monotonic() + 6.0)
                res = _anneal_lift(d, D, k, order, MT, rng, end)
                if res is not None:
                    consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return fb_n, fb_e
    return best[0], best[1]
