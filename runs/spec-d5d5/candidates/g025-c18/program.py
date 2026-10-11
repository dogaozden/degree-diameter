"""Construction for bipartite (d, D) graphs.

Structured baselines:
  D = 2: K_{d,d}, which meets the Moore bound.
  D = 3: incidence graph of PG(2, q), with q the largest prime power <= d - 1.
  D = 4: incidence graph of the generalized quadrangle W(q), with q + 1 <= d.

Main search (D >= 3, for any order above the current best):
  Bi-Cayley lifts A_x ~ B_{x*g} (g in S) over semidirect products
  Z_m x|_r Z_k. The search uses numpy-vectorized frontier BFS on the
  group table, and simulated annealing on the number of vertex pairs at
  distance > D from A_0 and B_0. Left translation is an automorphism, so
  these two sources suffice. Every result is re-checked with lib.is_valid,
  and K_{d,d} is the fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Structured baselines.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Vectorized bi-Cayley search over Z_m x|_r Z_k.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10        # groups tried per order N before moving on
ITERS = 12000          # annealing steps per group
SLICE = 6.0            # seconds spent on one order N before changing N
WINDOW = 6             # random window above the current lower bound
_TABLES = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_table(m, k, r):
    """Return (T, inv): T[x, g] = x*g and inv[g] = g^-1 for the element a*k+b of Z_m x|_r Z_k."""
    N = m * k
    idx = np.arange(N, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    T = A * k + B
    inv = np.argmax(T == 0, axis=1).astype(np.int64)
    return T, inv


def _table(m, k, r):
    key = (m, k, r)
    if key not in _TABLES:
        if len(_TABLES) > 24:
            _TABLES.clear()
        _TABLES[key] = _group_table(m, k, r)
    return _TABLES[key]


def _unreached(T, S, Sinv, N, D):
    """Pairs (source, vertex) at distance > D, summed over sources A_0 and B_0.

    A_x ~ B_{x*g} for g in S. Frontier BFS: B-neighbours of A_x are T[x, S],
    A-neighbours of B_y are T[y, Sinv].
    """
    total = 0
    for side in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if side == 0:
            seenA[0] = True
            fA = np.zeros(1, dtype=np.int64)
            fB = np.zeros(0, dtype=np.int64)
        else:
            seenB[0] = True
            fB = np.zeros(1, dtype=np.int64)
            fA = np.zeros(0, dtype=np.int64)
        for _ in range(D):
            if fA.size == 0 and fB.size == 0:
                break
            tb = np.zeros(N, dtype=bool)
            if fA.size:
                tb[T[fA][:, S].ravel()] = True
            tb &= ~seenB
            ta = np.zeros(N, dtype=bool)
            if fB.size:
                ta[T[fB][:, Sinv].ravel()] = True
            ta &= ~seenA
            seenB |= tb
            seenA |= ta
            fA = np.flatnonzero(ta)
            fB = np.flatnonzero(tb)
        total += 2 * N - int(seenA.sum()) - int(seenB.sum())
    return total


def _anneal(T, inv, N, d, D, rng, deadline, iters):
    """Simulated annealing on a connection set S (0 fixed in S) with zero unreached pairs."""
    if d < 2 or N <= d:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    Sa = np.array(S, dtype=np.int64)
    cur = _unreached(T, Sa, inv[Sa], N, D)
    t0, t1 = 2.0, 0.15
    for it in range(iters):
        if cur == 0:
            break
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        temp = t0 * (t1 / t0) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        Sa = np.array(S, dtype=np.int64)
        v = _unreached(T, Sa, inv[Sa], N, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = v
        else:
            S[i] = old
    return S if cur == 0 else None


def _search_lift(d, D, N, rng, deadline):
    """Try groups of order N until one yields a valid bi-Cayley lift; return (S, T) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        T, inv = _table(m, k, r)
        S = _anneal(T, inv, N, d, D, rng, deadline, ITERS)
        if S is not None:
            return S, T
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bi-Cayley lift search above the current best order.
    target = best[0] // 2 + 1
    while best[0] < moore and time.monotonic() < deadline:
        N = target
        if 2 * N > moore:
            break
        if N <= d:
            target += 1
            continue
        slice_end = min(deadline, time.monotonic() + SLICE)
        res = _search_lift(d, D, N, rng, slice_end)
        if res is not None:
            S, T = res
            Sl = [int(g) for g in S]
            cols = T[:, Sl].tolist()
            edges = [(x, N + int(cols[x][j])) for x in range(N) for j in range(len(Sl))]
            consider(2 * N, edges)
            target = best[0] // 2 + 1
        else:
            target = best[0] // 2 + 1 + rng.randrange(WINDOW)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
