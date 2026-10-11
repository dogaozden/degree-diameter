import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact or near-exact algebraic families (kept as safe baselines).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _cycle(n):
    """Cycle on n vertices (bipartite when n is even)."""
    return n, [(i, (i + 1) % n) for i in range(n)]


# ----------------------------------------------------------------------------
# New main construction: Haar graphs over finite groups.
#
# For a group G of order N and a connection set S of size d, the Haar graph
# H(G, S) has vertices A_g and B_h (g, h in G), with A_g ~ B_{g s} for s in S.
# It is bipartite and d-regular. Left multiplication is an automorphism, so
# the diameter condition reduces to two BFS runs, from A_e and from B_e.
#
# Groups are semidirect products Z_a x|_r Z_b (element (x, y) coded x*b + y,
# product (x, y)(u, v) = (x + r^y u, y + v)). Non-abelian groups are preferred.
# Search: simulated annealing over S, with cost = total unreached pairs.
# The search grows the group order adaptively and always keeps a valid best.
# ----------------------------------------------------------------------------

def _groups_of_order(N):
    """All (a, b, r) with a*b = N describing Z_a x|_r Z_b (r^b = 1 mod a, gcd(r, a) = 1)."""
    out = []
    for a in range(1, N + 1):
        if N % a:
            continue
        b = N // a
        if a == 1:
            out.append((1, b, 0))
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                out.append((a, b, r))
    return out


def _group_table(a, b, r):
    """Return (N, mul, inv) as numpy arrays for Z_a x|_r Z_b."""
    N = a * b
    x = np.arange(N, dtype=np.int64)
    A = x // b
    Bc = x % b
    P = np.array([pow(r, t, a) if a > 1 else 0 for t in range(b)], dtype=np.int64)
    mul = ((A[:, None] + P[Bc][:, None] * A[None, :]) % a) * b + (Bc[:, None] + Bc[None, :]) % b
    inv = np.zeros(N, dtype=np.int64)
    rows, cols = np.nonzero(mul == 0)
    inv[rows] = cols
    return N, mul, inv


def _set_col(nb, N, mul, inv, i, x):
    """Set column i of the neighbour matrix for connection element x.

    Rows 0..N-1 are A-vertices (neighbours B_{g x}); rows N..2N-1 are B-vertices
    (neighbours A_{h x^{-1}}).
    """
    nb[:N, i] = N + mul[:, x]
    nb[N:, i] = mul[:, inv[x]]


def _cost(nb, N, D):
    """Unreached (representative, vertex) pairs for representatives A_e and B_e."""
    R = np.zeros((2 * N, 2), dtype=bool)
    R[0, 0] = True
    R[N, 1] = True
    for _ in range(D):
        new = R | R[nb].any(axis=1)
        if np.array_equal(new, R):
            break
        R = new
    return 4 * N - int(R.sum())


def _anneal(d, D, N, mul, inv, rng, deadline, iters):
    """Simulated annealing over the connection set S. Returns S on success, else None."""
    S = rng.sample(range(N), d)
    nb = np.empty((2 * N, d), dtype=np.int64)
    for i, x in enumerate(S):
        _set_col(nb, N, mul, inv, i, x)
    cur = _cost(nb, N, D)
    inS = set(S)
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in inS:
            continue
        old = S[i]
        temp = max(0.3, 1.5 * (1.0 - t / iters))
        _set_col(nb, N, mul, inv, i, x)
        c = _cost(nb, N, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S[i] = x
            inS.discard(old)
            inS.add(x)
            cur = c
        else:
            _set_col(nb, N, mul, inv, i, old)
    if cur == 0:
        return S
    return None


def _haar_edges(N, mul, S):
    """Return (2N, edges) for the Haar graph of the group with table mul and set S."""
    edges = []
    for g in range(N):
        for s in S:
            edges.append((g, N + int(mul[g, s])))
    return 2 * N, edges


def _try_order(d, D, N, rng, deadline, until):
    """Try to find a Haar graph over a group of order N. Returns (2N, edges) or None."""
    groups = _groups_of_order(N)
    if not groups:
        return None
    nonab = [g for g in groups if g[1] > 1 and g[2] != 1]
    stop = min(deadline, until)
    while time.monotonic() < stop:
        if nonab and rng.random() < 0.8:
            a, b, r = rng.choice(nonab)
        else:
            a, b, r = rng.choice(groups)
        _, mul, inv = _group_table(a, b, r)
        S = _anneal(d, D, N, mul, inv, rng, stop, 3000)
        if S is not None:
            return _haar_edges(N, mul, S)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        # K_{d,d} is the bipartite Moore graph for diameter 2.
        return lib.haar_graph(d, range(d))
    if d == 2:
        n, e = _cycle(2 * D)  # Moore-optimal for max degree 2
        if lib.is_valid(n, e, d, D):
            return n, e

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Exact constructions for small cases.
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

    # Main search: Haar graphs over groups, with an adaptive jump size.
    half = best_n // 2  # group order of the current best
    delta = max(1, half // 16)
    while time.monotonic() < deadline:
        N = half + rng.randint(1, delta)
        res = _try_order(d, D, N, rng, deadline, time.monotonic() + 2.5)
        if res is not None and consider(res[0], res[1]):
            half = best_n // 2
            delta = max(1, min(2 * delta, half // 8 + 1))
        else:
            delta = max(1, delta // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
