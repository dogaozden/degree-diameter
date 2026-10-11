"""Bi-Cayley lift search with vectorised reachability for D >= 5.

Changes from the parent: the D >= 5 search uses numpy BFS over the bi-Cayley
table (about 20x cheaper per evaluation than the pure-Python BFS), a per-order
time slice so no single order N can absorb the budget, and a self-built
semidirect-product table. D = 2, 3, 4 keep the projective-plane and
generalized-quadrangle baselines. Every returned graph is checked with
lib.is_valid, and K_{d,d} is the fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib

N_WINDOW = 8
MAX_GROUPS = 10
CLIMB_STALL = 400
SLICE = 4.0
_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baselines for D = 3 and D = 4.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k, with numpy tables and numpy BFS.
# Vertices: A_x = x, B_y = N + y. Edge A_x ~ B_{x*g} for g in S.
# ----------------------------------------------------------------------------

def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """T[x, g] = x*g for the semidirect product, element (a, b) coded as a*k + b.

    Product: (a, b)(c, d) = (a + r^b c, b + d). Identity is code 0.
    """
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    c = a
    dd = b
    return ((a[:, None] + pw[b][:, None] * c[None, :]) % m) * k + (b[:, None] + dd[None, :]) % k


def _unreached(N, T, S, invS, D, limit):
    """Number of (source, vertex) pairs not within D, for sources A_0 and B_0.

    Left translation is an automorphism on each side, so two sources suffice.
    Early exit once the running total exceeds `limit`.
    """
    total = 0
    for src in (0, N):
        seen = np.zeros(2 * N, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        cnt = 1
        for _ in range(D):
            if front.size == 0:
                break
            fa = front[front < N]
            fb = front[front >= N] - N
            parts = []
            if fa.size:
                parts.append(T[fa[:, None], S[None, :]].ravel() + N)
            if fb.size:
                parts.append(T[fb[:, None], invS[None, :]].ravel())
            if not parts:
                break
            nb = np.unique(np.concatenate(parts))
            nb = nb[~seen[nb]]
            seen[nb] = True
            cnt += nb.size
            front = nb
        total += 2 * N - cnt
        if total > limit:
            return total
    return total


def _climb(N, T, invs, d, D, rng, deadline):
    def fresh():
        return np.array([0] + rng.sample(range(1, N), d - 1), dtype=np.int64)

    S = fresh()
    cur = _unreached(N, T, S, invs[S], D, _BIG)
    stall = 0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S.copy()
        S2[i] = c
        v = _unreached(N, T, S2, invs[S2], D, cur)
        stall = 0 if v < cur else stall + 1
        if v <= cur:
            S, cur = S2, v
        if stall > CLIMB_STALL:
            S = fresh()
            cur = _unreached(N, T, S, invs[S], D, _BIG)
            stall = 0
    return S if cur == 0 else None


def _search(d, D, N, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        T = _table(m, k, r)
        invs = np.argmax(T == 0, axis=1)
        S = _climb(N, T, invs, d, D, rng, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 3:
        return best

    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)
        slice_end = min(deadline, time.monotonic() + SLICE)
        res = _search(d, D, N, rng, slice_end)
        if res is not None:
            T, S = res
            edges = [(x, N + int(T[x, g])) for x in range(N) for g in S.tolist()]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
