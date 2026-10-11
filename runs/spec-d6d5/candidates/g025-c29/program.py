import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane, Araujo-Pardo-Lopez, generalized quadrangle,
# and K_{d,d}. Every candidate is checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _baseline(d, D):
    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    cands = []
    for fn in (lambda: _best_pg(d), lambda: _araujo(d),
               lambda: _best_gq(d) if D >= 4 else None):
        try:
            c = fn()
            if c is not None:
                cands.append(c)
        except Exception:
            pass
    for n, e in cands:
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley graphs over semidirect products Z_m x| Z_k.
#
# Vertices A_g and B_h, g, h in G. The connection set S (|S| = d, identity in S
# WLOG) gives edges A_g -- B_{g s} for s in S. Such a graph is d-regular and
# bipartite, and the group acts by left multiplication. So the diameter is
# certified by two BFS runs, one from A_e and one from B_e, using numpy gathers.
# Search is a fast hill-climb over S, across many group orders, ratcheted just
# above the incumbent order.
# ----------------------------------------------------------------------------

def _table(m, k, r):
    """Multiplication table M[x, y] of Z_m x| Z_k with r^k = 1 mod m, element (a, b) coded a*k+b."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    return ((A + pw[B] * C) % m) * k + (B + Dd) % k


def _group_options(G, kmax=12):
    """All (m, k, r) with m*k = G, k <= kmax, giving a valid semidirect product."""
    opts = []
    for k in range(1, min(kmax, G) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _cost(PI, QI, G, D):
    """Unreached pairs for the bi-Cayley graph. Zero means diameter <= D.

    PI[i][g] = g*s_i (neighbour of A_g in B); QI[i][h] = h*s_i^{-1} (neighbour of B_h in A).
    """
    # BFS from A_e: covers A-A and A-B pairs (by left translation).
    visA = np.zeros(G, dtype=bool)
    visB = np.zeros(G, dtype=bool)
    visA[0] = True
    fr = visA.copy()
    on_a = True
    for _ in range(D):
        if on_a:
            new = fr[QI].any(axis=0) & ~visB
            visB |= new
        else:
            new = fr[PI].any(axis=0) & ~visA
            visA |= new
        fr = new
        on_a = not on_a
        if not fr.any():
            break
    total = (G - int(visA.sum())) + (G - int(visB.sum()))

    # BFS from B_e: covers remaining B-B pairs.
    visA2 = np.zeros(G, dtype=bool)
    visB2 = np.zeros(G, dtype=bool)
    visB2[0] = True
    fr = visB2.copy()
    on_b = True
    for _ in range(D):
        if on_b:
            new = fr[PI].any(axis=0) & ~visA2
            visA2 |= new
        else:
            new = fr[QI].any(axis=0) & ~visB2
            visB2 |= new
        fr = new
        on_b = not on_b
        if not fr.any():
            break
    total += G - int(visB2.sum())
    return total


def _eval(M, inv, S, G, D):
    Sa = np.asarray(S, dtype=np.int64)
    PI = M[:, Sa].T
    QI = M[:, inv[Sa]].T
    return _cost(PI, QI, G, D)


def _search_group(d, D, G, M, inv, rng, deadline, iters):
    """Hill-climb a connection set S (identity included) to make the bi-Cayley graph diameter <= D."""
    S = [0] + rng.sample(range(1, G), d - 1)
    c = _eval(M, inv, S, G, D)
    for _ in range(iters):
        if c == 0:
            return S, 0
        if time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        T = list(S)
        T[i] = x
        ct = _eval(M, inv, T, G, D)
        if ct <= c or rng.random() < math.exp(-(ct - c) / 1.5):
            S, c = T, ct
    if c == 0:
        return S, 0
    return None, c


def _edges(M, S, G):
    return [(g, G + int(M[g, s])) for g in range(G) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    best = _baseline(d, D)
    best_n = best[0]
    if best_n >= lib._moore_bound(d, D):
        return best

    # Ratchet: search group orders just above the incumbent, bi-Cayley graphs
    # with exactly d darts each (degree d, bipartite by construction).
    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        G = lo + rng.randrange(0, 8)
        opts = _group_options(G)
        if not opts:
            continue
        m, k, r = rng.choice(opts)
        M = _table(m, k, r)
        inv = np.argmax(M == 0, axis=1)
        S, _c = _search_group(d, D, G, M, inv, rng, deadline, 3000)
        if S is not None:
            n2 = 2 * G
            e2 = _edges(M, S, G)
            if n2 > best_n and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
                best_n = n2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
