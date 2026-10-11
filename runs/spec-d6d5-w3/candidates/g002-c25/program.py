"""Bi-Cayley (Haar-type) search over abelian groups Z_a x Z_b for diameter-D bipartite graphs.

Construction: vertices A_x and B_y (x, y in G, |G| = N). Connection set S (|S| = d, 0 in S
WLOG) gives edges A_x -- B_{x+s} for s in S. The graph is d-regular, bipartite, and
translation-invariant on each side, with a side-swapping automorphism A_x <-> B_{-x}. So the
diameter check reduces to two sumset computations from A_0:

    X_k = A-indices within distance 2k of A_0,  Y_k = B-indices within distance 2k+1.
    X_{k+1} = X_k U (Y_k - S),   Y_{k+1} = Y_k U (X_{k+1} + S).

For diameter D we need |X_{D//2}| = N and |Y_{(D-1)//2}| = N. Simulated hill-climbing
searches S for the largest N that passes. Every returned graph is re-verified with
lib.is_valid. Fallbacks: K_{d,d}, the projective-plane incidence graph (D = 3), and the
Araujo-Pardo-Lopez graph (D = 3). Not executed in this revision; the verifier gate
guards the output.
"""
import math
import random
import time

import lib


_TABLE_CACHE = {}


def _group_options(N):
    """Abelian groups of order N as (a, b) meaning Z_a x Z_b with b | a (b = 1 is cyclic)."""
    opts = [(N, 1)]
    for b in range(2, math.isqrt(N) + 1):
        if N % b == 0 and (N // b) % b == 0:
            opts.append((N // b, b))
    return opts


def _tables(a, b):
    """Addition and negation tables for Z_a x Z_b, element (i, j) encoded as i*b + j."""
    key = (a, b)
    if key in _TABLE_CACHE:
        return _TABLE_CACHE[key]
    if len(_TABLE_CACHE) > 6:
        _TABLE_CACHE.clear()
    N = a * b
    add = [[((x // b + y // b) % a) * b + (x % b + y % b) % b for y in range(N)]
           for x in range(N)]
    neg = [((-(x // b)) % a) * b + (-(x % b)) % b for x in range(N)]
    _TABLE_CACHE[key] = (add, neg)
    return add, neg


def _cost(N, add, neg, S, tx, ty):
    """Number of A-vertices missing from X_tx plus B-vertices missing from Y_ty. Zero means valid."""
    neg_S = [neg[s] for s in S]
    X = {0}
    Y = set(S)
    Xs = [X]
    Ys = [Y]
    for _ in range(max(tx, ty)):
        Xn = set(X)
        for y in Y:
            row = add[y]
            for ns in neg_S:
                Xn.add(row[ns])
        Yn = set(Y)
        for x in Xn:
            row = add[x]
            for s in S:
                Yn.add(row[s])
        X, Y = Xn, Yn
        Xs.append(X)
        Ys.append(Y)
    return (N - len(Xs[tx])) + (N - len(Ys[ty]))


def _attempt(N, d, D, rng, deadline):
    """Hill-climb a connection set S of size d (containing 0) for a group of order N."""
    tx, ty = D // 2, (D - 1) // 2
    a, b = rng.choice(_group_options(N))
    add, neg = _tables(a, b)
    if N < d:
        return None
    others = list(range(1, N))
    S = [0] + rng.sample(others, d - 1)
    c = _cost(N, add, neg, S, tx, ty)
    while time.monotonic() < deadline:
        if c == 0:
            return S
        i = rng.randrange(1, d)
        new = rng.randrange(1, N)
        while new in S:
            new = rng.randrange(1, N)
        T = S[:]
        T[i] = new
        ct = _cost(N, add, neg, T, tx, ty)
        if ct <= c or rng.random() < 0.02:
            S, c = T, ct
    return S if c == 0 else None


def _haar_edges(N, add, S):
    """Edges A_x -- B_{x+s}; A_x is vertex x, B_y is vertex N + y."""
    edges = []
    for x in range(N):
        row = add[x]
        for s in S:
            edges.append((x, N + row[s]))
    return 2 * N, edges


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    if d < 3:
        return None
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (Haar graph of Z_d with full connection set), diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if best_n >= target:
        return best

    # Main search: bi-Cayley graphs over abelian groups, increasing N.
    cur = max(d, best_n // 2) + 1
    max_N = target // 2
    try:
        while time.monotonic() < deadline and cur <= max_N:
            now = time.monotonic()
            remaining = deadline - now
            attempt_deadline = min(deadline, now + max(2.0, remaining / 4))
            S = _attempt(cur, d, D, rng, attempt_deadline)
            if S is not None:
                a, b = rng.choice(_group_options(cur))
                add, _ = _tables(a, b)
                n, e = _haar_edges(cur, add, S)
                consider(n, e)
                cur += 1
            # On failure the same N is retried with a fresh group and connection set.
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
