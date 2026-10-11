import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact families for small D (kept from the parent; they return instantly).
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
# Bold change: bi-Cayley graphs with ONE base vertex per side over a finite
# group G (semidirect products Z_m x| Z_k2, possibly dihedral-like).
#
# Vertices: A_g = g and B_h = G + h. Connection set S = {s_0..s_{d-1}}
# (distinct group elements). A_g ~ B_{g*s} for every s in S. Then B_h is
# adjacent to A_{h*s^{-1}}, so the graph is d-regular and bipartite with
# 2|G| vertices. Left multiplication is an automorphism, so the diameter
# check only needs the two representatives A_e and B_e.
#
# Search: simulated annealing over the d connection elements directly
# (not layered k-block lifts as in the parent). Cost = number of vertices
# unreached from A_e or B_e within distance D. Groups of order G are tried
# in increasing order just above the current best half-order.
# ----------------------------------------------------------------------------

_POP4 = np.array([0, 1, 1, 2], dtype=np.int64)


def _groups_of_order(G, rng):
    """Return a list of (m, k2, r) describing Z_m x| Z_k2 of order G (cyclic when k2 = 1)."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        found = None
        if k2 == 2 and m > 2:
            # Dihedral-type: r = -1 with r^2 = 1 mod m.
            if math.gcd(m - 1, m) == 1:
                found = m - 1
        if found is None:
            for _ in range(60):
                r = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                    found = r
                    break
        if found is not None:
            out.append((m, k2, found))
    return out


def _group_tables(m, k2, r):
    """Return (Ts, Invs) with Ts[s, g] = g*s and Invs[s, h] = g such that g*s = h.

    Element a*k2 + b encodes (a, b), with (a, b)(c, e) = (a + r^b c, b + e).
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    Invs[np.arange(G)[:, None], Ts] = x[None, :]
    return Ts, Invs


def _anneal(d, D, G, Ts, Invs, rng, deadline, iters):
    """Search for d distinct connection elements giving diameter <= D. Returns (S, nbr) or None."""
    S = rng.sample(range(G), d)
    nbr = np.empty((d, 2 * G), dtype=np.int64)

    def fill(l, s):
        nbr[l, :G] = G + Ts[s]
        nbr[l, G:] = Invs[s]

    for l, s in enumerate(S):
        fill(l, s)

    def cost_of():
        reach = np.zeros(2 * G, dtype=np.int64)
        reach[0] = 1       # bit 0: representative A_e
        reach[G] = 2       # bit 1: representative B_e
        for _ in range(D):
            new = reach | np.bitwise_or.reduce(reach[nbr], axis=0)
            if np.array_equal(new, reach):
                break
            reach = new
        return int((2 - _POP4[reach]).sum())

    cost = cost_of()
    for t in range(iters):
        if cost == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        temp = 1.5 * (1.0 - t / iters) + 0.1
        l = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[l]
        S[l] = new
        fill(l, new)
        c2 = cost_of()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l] = old
            fill(l, old)

    if cost != 0:
        return None
    return S, nbr


def _edges_from_nbr(G, nbr):
    """Edges A_g -- B_{g*s}: each edge listed once from its A endpoint."""
    d = nbr.shape[0]
    edges = []
    for l in range(d):
        for g in range(G):
            edges.append((g, int(nbr[l, g])))
    return edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

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

    # Exact constructions return immediately (calibration-style cases).
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

    # Bold search: bi-Cayley graphs over groups of order just above best_n / 2.
    if d >= 3 and D >= 3:
        cache = {}
        while time.monotonic() < deadline:
            lo = best_n // 2 + 1
            G = lo + rng.randrange(0, 12)
            if G not in cache:
                cache[G] = _groups_of_order(G, rng)
            opts = cache[G]
            if not opts or G < d:
                continue
            m, k2, r = rng.choice(opts)
            Ts, Invs = _group_tables(m, k2, r)
            res = _anneal(d, D, G, Ts, Invs, rng, deadline, 2500)
            if res is not None:
                _, nbr = res
                consider(2 * G, _edges_from_nbr(G, nbr))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
