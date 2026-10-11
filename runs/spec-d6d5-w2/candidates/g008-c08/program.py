import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Structured baselines (kept as safe fallbacks and for D = 3, 4).
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 9 for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over metacyclic groups Z_m x|_r Z_k with ONE base orbit per side.
#
# Vertices A_g and B_h for g, h in G (|G| = G). Connection set S of d distinct
# group elements: A_g ~ B_{g*s} for s in S. The group acts by left
# multiplication, which is an automorphism, so only two sources must be checked:
# A_e (reaches all A within 4 and all B within 5) and B_e (the same, mirrored).
#
# The search is a simulated annealing over S. The cost is the number of
# (source, vertex) pairs not reached within D, computed with numpy permutation
# gathers. The cost is zero exactly when the lift has diameter <= D.
# ----------------------------------------------------------------------------

def _random_group(G, rng):
    """Return (m, k, r) with m*k = G, giving Z_m x|_r Z_k, or None."""
    ks = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not ks:
        return None
    for _ in range(30):
        k = rng.choice(ks + [1, 1])
        if G % k != 0 or G // k < 2:
            continue
        m = G // k
        if k == 1:
            return (m, 1, 1)
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if cands:
            return (m, k, rng.choice(cands))
    return None


def _group_table(m, k, r):
    """Vectorised multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    A = x // k
    B = x % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    # (a, b) * (c, e) = (a + r^b c, b + e)
    T = ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    return T.astype(np.int64)


def _cost(TT, inv, S, D, G):
    """Unreached (source, vertex) pairs over both sources A_e and B_e; zero means diameter <= D."""
    fwd = [TT[s] for s in S]
    bwd = [TT[inv[s]] for s in S]
    total = 0
    for src_side in (0, 1):
        vis = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        vis[src_side][0] = True
        f = np.array([0], dtype=np.intp)
        side = src_side
        for _ in range(D):
            perms = fwd if side == 0 else bwd
            nb = np.zeros(G, dtype=bool)
            for p in perms:
                nb[p[f]] = True
            new = nb & ~vis[1 - side]
            vis[1 - side] |= new
            side = 1 - side
            f = np.flatnonzero(new)
            if f.size == 0:
                break
        total += 2 * G - int(vis[0].sum()) - int(vis[1].sum())
    return total


def _search(TT, inv, G, d, D, rng, deadline, iters):
    """Anneal a d-element connection set in G. Returns S with cost 0, or None."""
    if G < d:
        return None
    S = rng.sample(range(G), d)
    c = _cost(TT, inv, S, D, G)
    temp = 3.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost(TT, inv, S2, D, G)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, c = S2, c2
        temp = max(0.3, temp * 0.998)
    return S if c == 0 else None


def _lift_edges(G, T, S):
    """Edges of the bi-Cayley graph: A_g = g, B_h = G + h, with A_g ~ B_{g*s}."""
    E = []
    for s in S:
        col = T[:, s]
        for g in range(G):
            E.append((g, G + int(col[g])))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: bi-Cayley lifts over metacyclic groups, with a numpy cost.
    while time.monotonic() < deadline:
        mh = lib.moore_bound(d, D) // 2
        lo = max(best_n // 2 + 1, int(0.40 * mh), d)
        hi = min(mh, 1000, max(lo + 8, int(0.52 * mh)))
        if lo > hi:
            break
        G = rng.randint(lo, hi)
        grp = _random_group(G, rng)
        if grp is None:
            continue
        m, k, r = grp
        T = _group_table(m, k, r)
        inv = np.empty(G, dtype=np.int64)
        rows, cols = np.nonzero(T == 0)
        inv[rows] = cols
        TT = np.ascontiguousarray(T.T)

        S = _search(TT, inv, G, d, D, rng, deadline, 2000)
        if S is not None:
            n, e = _lift_edges(G, T, S)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
