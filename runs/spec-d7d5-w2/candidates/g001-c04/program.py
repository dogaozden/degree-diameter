import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and safe baselines.
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
# Bi-Cayley graphs over a single finite group G (new family relative to the
# multi-base-vertex lifts of the parent).
#
# Vertices: A_g = g (0 <= g < G), B_h = G + h.
# Layer s (s in S, |S| = d, distinct) is the matching A_g ~ B_{g*s}.
# Left multiplication by any x is an automorphism, so only two representatives
# (A_e and B_e) need to reach everything within D steps.
# Cost = number of (representative, vertex) pairs at distance > D.
# Search: simulated annealing over the connection set S, one element at a time.
# ----------------------------------------------------------------------------

_SLICE = 4.0  # seconds per annealing trial


def _finish_table(M):
    """Given the multiplication table M[g, s] = g*s, return (M, M.T contiguous, inverse index)."""
    invs = np.argmax(M == 0, axis=1)  # invs[s] = s^{-1}, since M[s, g] = 0 iff g = s^{-1}
    MT = np.ascontiguousarray(M.T)
    return M, MT, invs


def _group_tables(G, rng):
    """Multiplication table of a random group of order G (semidirect or direct product of cyclics)."""
    if rng.random() < 0.5:
        divs = [k for k in range(2, G) if G % k == 0]
        if divs:
            k = rng.choice(divs)
            m = G // k
            r = None
            if m >= 2:
                for _ in range(60):
                    c = rng.randrange(2, m) if m > 2 else 1
                    if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                        r = c
                        break
            if r is not None:
                x = np.arange(G, dtype=np.int64)
                a = x // k
                b = x % k
                pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
                M = ((a[:, None] + pw[b[:, None]] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
                return _finish_table(M)
    # Direct product Z_a x Z_b with a*b = G (b = 1 gives the cyclic group).
    divs = [b for b in range(1, G + 1) if G % b == 0]
    b = rng.choice(divs)
    a = G // b
    x = np.arange(G, dtype=np.int64)
    i = x // b
    j = x % b
    M = ((i[:, None] + i[None, :]) % a) * b + (j[:, None] + j[None, :]) % b
    return _finish_table(M)


def _layer(s, G, MT, invs):
    """Neighbour map (length 2G) of the matching for connection element s.

    A_g (index g) -> B_{g*s} (index G + MT[s, g]).
    B_h (index G+h) -> A_{h*s^{-1}} (index MT[invs[s], h]).
    """
    return np.concatenate((G + MT[s], MT[invs[s]]))


def _cost(nbs, G, D):
    """Unreached (representative, vertex) pairs within distance D, over the representatives A_e and B_e."""
    N = 2 * G
    reach = np.zeros((2, N), dtype=bool)
    reach[0, 0] = True
    reach[1, G] = True
    for _ in range(D):
        new = reach.copy()
        for nb in nbs:
            new |= reach[:, nb]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * N - int(np.count_nonzero(reach))


def _anneal(G, tabs, d, D, rng, deadline, iters):
    """Search for a connection set S of d distinct elements with zero cost. Returns S or None."""
    M, MT, invs = tabs
    S = rng.sample(range(G), d)
    nbs = [_layer(s, G, MT, invs) for s in S]
    cost = _cost(nbs, G, D)
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0:
            break
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.5, 0.03 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[l]
        old_nb = nbs[l]
        S[l] = new
        nbs[l] = _layer(new, G, MT, invs)
        c2 = _cost(nbs, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l] = old
            nbs[l] = old_nb
    if cost == 0:
        return S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is Moore-optimal for D = 2.
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

    # Main search: bi-Cayley graphs over groups of order G, so n = 2G.
    while time.monotonic() < deadline:
        G = max(best_n // 2 + 1, d + 1) + rng.choice([0, 0, 1, 1, 2, 3])
        tabs = _group_tables(G, rng)
        slice_end = min(deadline, time.monotonic() + _SLICE)
        S = _anneal(G, tabs, d, D, rng, slice_end, 20000)
        if S is not None:
            M, MT, invs = tabs
            edges = []
            for s in S:
                for g in range(G):
                    edges.append((g, G + int(MT[s, g])))
            consider(2 * G, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
