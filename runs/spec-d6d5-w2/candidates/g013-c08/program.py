import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines (fast, always tried first).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
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
    """W(q) for the largest prime power q <= min(d - 1, 7)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over metacyclic groups Z_m x|_r Z_k.
#
# Vertices A_x = x and B_y = G + y, with x in G. Connection set S (|S| = d, distinct).
# Edge A_x ~ B_{x*s} for s in S. Left multiplication is an automorphism, so the
# diameter is at most D iff BFS from A_e and from B_e reaches everything within D.
# Right-multiplying S by a fixed element gives an isomorphic graph, so we fix 0 in S.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random (m, k, r) with m*k = G describing Z_m x|_r Z_k (r = 1 is a direct product)."""
    opts = []
    for k in range(1, G + 1):
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
    if not opts:
        return None
    nonab = [o for o in opts if o[1] > 1 and o[2] != 1]
    if nonab and rng.random() < 0.75:
        return rng.choice(nonab)
    return rng.choice(opts)


def _table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    left = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    right = (b[:, None] + b[None, :]) % k
    return left * k + right


def _bad(nbrA, nbrB, G, D):
    """Unreached (vertex, source) count from A_e and B_e within D steps; zero means valid."""
    total = 0
    for side in (0, 1):
        sA = np.zeros(G, dtype=bool)
        sB = np.zeros(G, dtype=bool)
        if side == 0:
            sA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = np.empty(0, dtype=np.int64)
        else:
            sB[0] = True
            fB = np.array([0], dtype=np.int64)
            fA = np.empty(0, dtype=np.int64)
        for _ in range(D):
            if fA.size == 0 and fB.size == 0:
                break
            nB = nbrA[fA].ravel()
            nA = nbrB[fB].ravel()
            nB = np.unique(nB[~sB[nB]])
            nA = np.unique(nA[~sA[nA]])
            sB[nB] = True
            sA[nA] = True
            fA, fB = nA, nB
        total += 2 * G - int(sA.sum()) - int(sB.sum())
    return total


def _search_group(M, G, d, D, deadline, rng):
    """Simulated annealing over connection sets S (0 in S, |S| = d). Returns S or None."""
    inv = np.argmax(M == 0, axis=1)

    def cost(S):
        Sa = np.asarray(S, dtype=np.int64)
        return _bad(M[:, Sa], M[:, inv[Sa]], G, D)

    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, G), d - 1)
        c = cost(S)
        T = 1.0
        for it in range(1200):
            if c == 0:
                return S
            if (it & 31) == 0 and time.monotonic() >= deadline:
                return None
            i = rng.randrange(1, d)
            x = rng.randrange(1, G)
            if x in S:
                continue
            S2 = S[:]
            S2[i] = x
            c2 = cost(S2)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                S, c = S2, c2
            T = max(0.05, T * 0.996)
    return None


def _bc_edges(M, S, G):
    E = [(x, G + int(M[x, s])) for x in range(G) for s in S]
    return 2 * G, E


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if best_n >= moore:
        return best

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= moore:
        return best

    # Bi-Cayley search over metacyclic groups, aimed above the current best order.
    if d >= 3 and D >= 3:
        lo = max(2 * d, best_n // 2 + 1, int(0.4 * moore / 2))
        hi = lo + max(4, lo // 6)
        per_group = 3.0
        while time.monotonic() < deadline:
            G = rng.randint(lo, hi)
            spec = _sample_group(G, rng)
            if spec is None:
                continue
            m, k, r = spec
            Gs = m * k
            M = _table(m, k, r)
            S = _search_group(M, Gs, d, D,
                              min(deadline, time.monotonic() + per_group), rng)
            if S is not None:
                n, e = _bc_edges(M, S, Gs)
                consider(n, e)
                lo = max(lo, Gs + 1)
                hi = lo + max(4, lo // 6)
            if best_n >= moore:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
