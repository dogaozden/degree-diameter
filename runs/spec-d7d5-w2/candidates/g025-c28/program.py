import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d. Diameter 3."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q). Diameter 4."""
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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: single-orbit bi-Cayley graphs (one base vertex per side).
#
# Let G be a finite group of order M with multiplication table `mul`.
# Pick a connection set S = {s_1..s_d} of d DISTINCT group elements.
# Vertices A_g = g and B_h = M + h. Edges: A_g ~ B_{g*s} for s in S.
# Then B_h ~ A_{h*s^-1}, so every vertex has degree exactly d and the
# graph is bipartite with 2M vertices.
#
# Left multiplication is an automorphism, so A-to-A, A-to-B, B-to-B and
# B-to-A distances all reduce to distances from the two sources A_e and B_e.
# Hence diameter <= D holds iff both sources reach all 2M vertices within D
# steps. This makes the cost cheap to evaluate, so simulated annealing over
# S runs thousands of times per group. The search raises the order M.
# ----------------------------------------------------------------------------

def _tables(m, k, r):
    """Multiplication and inverse tables for Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a+r^b c, b+e)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    mul = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.argmax(mul == 0, axis=1).astype(np.int64)
    return mul, inv


def _random_group(M, rng):
    """Random group of order M of the form Z_m x|_r Z_k with k | M, k <= 16, or None."""
    ks = [k for k in range(1, 17) if M % k == 0]
    k = rng.choice(ks)
    m = M // k
    if k == 1:
        rs = [1 % m]
    elif m == 1:
        rs = [0]
    else:
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    if not rs:
        return None
    r = rng.choice(rs)
    return _tables(m, k, r)


def _cost(M, mul, inv, S, D):
    """Return (unreached pairs from sources A_e and B_e, neighbour array) for connection set S."""
    Sv = np.asarray(S, dtype=np.int64)
    nbr = np.vstack([M + mul[:, Sv], mul[:, inv[Sv]]])
    N = 2 * M
    R = np.zeros((2, N), dtype=bool)
    R[0, 0] = True
    R[1, M] = True
    for _ in range(D):
        nxt = R.copy()
        for t in (0, 1):
            idx = np.flatnonzero(R[t])
            nxt[t, nbr[idx].ravel()] = True
        if np.array_equal(nxt, R):
            break
        R = nxt
    return 2 * N - int(R.sum()), nbr


def _anneal(M, d, D, mul, inv, rng, deadline, iters):
    """Simulated annealing over connection sets of d distinct elements. Returns S or None."""
    S = rng.sample(range(M), d)
    cost, _ = _cost(M, mul, inv, S, D)
    for t in range(iters):
        if cost == 0:
            break
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - t / iters) + 0.05
        j = rng.randrange(d)
        new = rng.randrange(M)
        if new in S:
            continue
        old = S[j]
        S[j] = new
        c2, _ = _cost(M, mul, inv, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[j] = old
    return S if cost == 0 else None


def _edges_from_S(M, mul, S):
    """Edge list of the bi-Cayley graph with 2M vertices."""
    Sv = np.asarray(S, dtype=np.int64)
    us = np.repeat(np.arange(M, dtype=np.int64), len(S))
    vs = M + mul[:, Sv].ravel()
    return 2 * M, [(int(u), int(v)) for u, v in zip(us.tolist(), vs.tolist())]


def _try_order(M, d, D, rng, deadline, iters):
    """Try a few random groups of order M with annealing. Returns (n, edges) or None."""
    if M < d:
        return None
    for _ in range(4):
        if time.monotonic() > deadline:
            return None
        g = _random_group(M, rng)
        if g is None:
            continue
        mul, inv = g
        S = _anneal(M, d, D, mul, inv, rng, deadline, iters)
        if S is not None:
            return _edges_from_S(M, mul, S)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Exact constructions for small D.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: single-orbit bi-Cayley graphs of increasing order.
    if d >= 2 and D >= 2:
        lo = best_n // 2 + 1  # a graph on 2M vertices beats best_n iff M >= lo
        while time.monotonic() < deadline:
            M = max(d, lo + rng.randrange(20))
            res = _try_order(M, d, D, rng, deadline, 3000)
            if res is not None and consider(res[0], res[1]):
                lo = best_n // 2 + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
