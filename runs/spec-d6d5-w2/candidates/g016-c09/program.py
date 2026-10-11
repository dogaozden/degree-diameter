import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Small helpers
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


# ----------------------------------------------------------------------------
# Baselines for D = 3 and D = 4 (projective plane, Araujo-Pardo-Lopez, GQ W(q)).
# ----------------------------------------------------------------------------

def _pg_incidence(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley / voltage lifts over explicit finite groups (D >= 4).
#
# Group G is given by a multiplication table M (identity = index 0).
# A lift with k "A" base vertices and k "B" base vertices uses d layers.
# Layer L pairs A_i with B_{perm_L[i]} with voltage volts[L][i]:
#     A_{i,g} ~ B_{perm_L[i], g * volts[L][i]}.
# Every vertex then has degree d, the graph is bipartite, and the vertex
# count is 2*k*G. Left multiplication is an automorphism, so the diameter is
# at most D iff every representative A_{i,1} and B_{j,1} reaches all vertices
# within D steps.
# ----------------------------------------------------------------------------

def _make_table(spec):
    """Multiplication table for a group spec. Returns (G, MT, invs) or None.

    MT[s, g] = g * s (right multiplication, stored transposed for fast columns).
    invs[x] = x^{-1}.
    """
    kind = spec[0]
    if kind == "aff":
        # AGL(1, p): element (u, b) with u in 1..p-1, coded as (u-1)*p + b.
        p = spec[1]
        G = p * (p - 1)
        idx = np.arange(G, dtype=np.int64)
        u = idx // p + 1
        b = idx % p
        nu = (u[:, None] * u[None, :]) % p
        nb = (u[:, None] * b[None, :] + b[:, None]) % p
        M = (nu - 1) * p + nb
    elif kind == "heis":
        # Heisenberg group of order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b').
        p = spec[1]
        G = p ** 3
        idx = np.arange(G, dtype=np.int64)
        a = idx // (p * p)
        bb = (idx // p) % p
        c = idx % p
        A = a[:, None]
        B = bb[:, None]
        C = c[:, None]
        A2 = a[None, :]
        B2 = bb[None, :]
        C2 = c[None, :]
        M = (((A + A2) % p) * p + (B + B2) % p) * p + (C + C2 + A * B2) % p
    else:
        # Semidirect Z_m x| Z_k with action r (r^k = 1 mod m): (a,b)(c,d) = (a + r^b c, b + d).
        _, m, k, r = spec
        G = m * k
        idx = np.arange(G, dtype=np.int64)
        a = idx // k
        b = idx % k
        pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
        A = a[:, None]
        Bc = b[:, None]
        A2 = a[None, :]
        B2 = b[None, :]
        M = ((A + pw[Bc] * A2) % m) * k + (Bc + B2) % k
    M = np.asarray(M, dtype=np.int64)
    ar = np.arange(G, dtype=np.int64)
    if not (np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar)):
        return None
    full = np.broadcast_to(ar, (G, G))
    if not (np.array_equal(np.sort(M, axis=1), full) and np.array_equal(np.sort(M, axis=0), full)):
        return None
    invs = np.argmax(M == 0, axis=1)
    MT = np.ascontiguousarray(M.T)
    return G, MT, invs


def _group_pool(lo, hi, rng):
    """Group specs with order in [lo, hi]: affine groups, Heisenberg groups, semidirect products."""
    specs = []
    for p in range(3, hi + 2):
        if _is_prime(p):
            o = p * (p - 1)
            if lo <= o <= hi:
                specs.append(("aff", p))
    for p in range(2, 40):
        if _is_prime(p) and lo <= p ** 3 <= hi:
            specs.append(("heis", p))
    for m in range(3, hi + 1):
        for k in range(2, hi // m + 1):
            o = m * k
            if o < lo or o > hi:
                continue
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not rs:
                continue
            for r in rng.sample(rs, min(len(rs), 3)):
                specs.append(("sd", m, k, r))
    return specs


def _dup(perms, volts, k, d):
    """True if two darts from the same A vertex would produce the same edge."""
    for i in range(k):
        seen = set()
        for L in range(d):
            key = (perms[L][i], volts[L][i])
            if key in seen:
                return True
            seen.add(key)
    return False


def _lift_adj(MT, invs, k, G, perms, volts, d):
    """Adjacency array (2kG, d) of the lift; A nodes first, then B nodes."""
    N = 2 * k * G
    Adj = np.empty((N, d), dtype=np.int64)
    for L in range(d):
        p = perms[L]
        v = volts[L]
        for i in range(k):
            j = p[i]
            s = int(v[i])
            Adj[i * G:(i + 1) * G, L] = (k + j) * G + MT[s]
            Adj[(k + j) * G:(k + j + 1) * G, L] = i * G + MT[int(invs[s])]
    return Adj


def _lift_cost(MT, invs, k, G, D, perms, volts, d):
    """Number of (representative, vertex) pairs not reached within D steps. Zero means valid."""
    Adj = _lift_adj(MT, invs, k, G, perms, volts, d)
    N = 2 * k * G
    total = 0
    srcs = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in srcs:
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = Adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _search_lift(MT, invs, k, G, d, D, deadline, rng, iters):
    """Simulated annealing over layer permutations and voltages. Returns (perms, volts) or None."""
    BIG = 10 ** 9

    def ev(perms, volts):
        if _dup(perms, volts, k, d):
            return BIG
        return _lift_cost(MT, invs, k, G, D, perms, volts, d)

    while time.monotonic() < deadline:
        if k > 1:
            perms = [rng.sample(range(k), k) for _ in range(d)]
        else:
            perms = [[0] for _ in range(d)]
        volts = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
        c = ev(perms, volts)
        T = 1.0
        for _ in range(iters):
            if c == 0 or time.monotonic() >= deadline:
                break
            T = max(0.05, T * 0.997)
            L = rng.randrange(d)
            if k > 1 and rng.random() < 0.25:
                a, b = rng.sample(range(k), 2)
                nperms = [row[:] for row in perms]
                nperms[L][a], nperms[L][b] = nperms[L][b], nperms[L][a]
                nv = volts
            else:
                i = rng.randrange(k)
                x = rng.randrange(G)
                if x == volts[L][i]:
                    continue
                nv = [row[:] for row in volts]
                nv[L][i] = x
                nperms = perms
            c2 = ev(nperms, nv)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                perms, volts, c = nperms, nv, c2
        if c == 0:
            return perms, volts
    return None


def _lift_edges(MT, invs, k, G, perms, volts, d):
    Adj = _lift_adj(MT, invs, k, G, perms, volts, d)
    n = 2 * k * G
    a = np.repeat(np.arange(k * G, dtype=np.int64), d)
    b = Adj[:k * G].ravel()
    return n, list(zip(a.tolist(), b.tolist()))


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _pg_incidence(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search for D >= 4: bi-Cayley / voltage lifts over a broad pool of groups.
    # Each round targets orders strictly above the current best.
    if D >= 4 and d >= 3:
        srng = random.Random(seed * 1000003 + d * 131 + D)
        cache = {}
        while time.monotonic() < deadline:
            k = srng.choice([1, 1, 1, 2, 2, 3])
            Gmin = best[0] // (2 * k) + 1
            Gmax = Gmin + max(8, Gmin // 5)
            key = (k, Gmin, Gmax)
            if key not in cache:
                cache[key] = _group_pool(Gmin, Gmax, srng)
            pool = cache[key]
            if not pool:
                continue
            spec = srng.choice(pool)
            tab = _make_table(spec)
            if tab is None:
                continue
            G, MT, invs = tab
            sub = min(deadline, time.monotonic() + 3.0)
            res = _search_lift(MT, invs, k, G, d, D, sub, srng, 600)
            if res is None:
                continue
            perms, volts = res
            n, e = _lift_edges(MT, invs, k, G, perms, volts, d)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
