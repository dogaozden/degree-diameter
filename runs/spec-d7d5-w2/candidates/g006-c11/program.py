import itertools
import math
import random
import time

import numpy as np

import lib


_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Safe baselines for small diameters.
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
# New construction for D >= 5: simulated annealing over d-regular bipartite
# graphs, using double-edge swaps (which keep regularity and bipartiteness).
#
# Vertices: A-vertex a -> a, B-vertex b -> M + b, for 0 <= a, b < M.
# The cost is the number of ordered vertex pairs at distance > D, computed
# with bitsets (one row of 64-bit words per vertex). The graph is grown by
# pair insertion, which adds two vertices and keeps degrees exactly d, and
# the annealer then repairs the new defects. Every accepted state has cost 0,
# and the final graph is checked with lib.is_valid before it is returned.
# ----------------------------------------------------------------------------

def _cost(M, d, D, A, B):
    """Number of ordered vertex pairs at distance > D in the bipartite graph given by edge lists A, B."""
    N = 2 * M
    A_arr = np.asarray(A, dtype=np.int64)
    B_arr = np.asarray(B, dtype=np.int64)
    oa = np.argsort(A_arr, kind="stable")
    na = B_arr[oa].reshape(M, d)          # neighbours of A-vertex a (B indices)
    ob = np.argsort(B_arr, kind="stable")
    nb = A_arr[ob].reshape(M, d)          # neighbours of B-vertex b (A indices)
    nbr = np.empty((N, d), dtype=np.int64)
    nbr[:M] = na + M
    nbr[M:] = nb
    W = (N + 63) // 64
    reach = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N, dtype=np.int64)
    reach[idx, idx >> 6] = np.uint64(1) << (idx & 63).astype(np.uint64)
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    pop = int(_POP8[reach.view(np.uint8)].sum())
    return N * N - pop


def _anneal(M, d, D, A, B, rng, deadline, iters):
    """Double-edge-swap annealing on the edge lists A, B (modified in place). Returns (ok, cost)."""
    E = len(A)
    keys = {A[t] * M + B[t] for t in range(E)}
    cost = _cost(M, d, D, A, B)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(E)
        j = rng.randrange(E)
        a1, b1 = A[i], B[i]
        a2, b2 = A[j], B[j]
        if a1 == a2 or b1 == b2:
            continue
        k1 = a1 * M + b2
        k2 = a2 * M + b1
        if k1 in keys or k2 in keys:
            continue
        B[i], B[j] = b2, b1
        nc = _cost(M, d, D, A, B)
        temp = max(0.3, 4.0 * (1.0 - t / iters))
        if nc <= cost or rng.random() < math.exp(-(nc - cost) / temp):
            keys.discard(a1 * M + b1)
            keys.discard(a2 * M + b2)
            keys.add(k1)
            keys.add(k2)
            cost = nc
        else:
            B[i], B[j] = b1, b2
    return cost == 0, cost


def _grow(M, d, A, B, rng):
    """Pair insertion: add one A-vertex x=M and one B-vertex y=M, keeping d-regularity. Returns (M+1, A, B) or None."""
    order = list(range(len(A)))
    rng.shuffle(order)
    usedA, usedB, chosen = set(), set(), []
    for t in order:
        if A[t] in usedA or B[t] in usedB:
            continue
        chosen.append(t)
        usedA.add(A[t])
        usedB.add(B[t])
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    ca = [A[t] for t in chosen]
    cb = [B[t] for t in chosen]
    cs = set(chosen)
    A2 = [A[t] for t in range(len(A)) if t not in cs]
    B2 = [B[t] for t in range(len(B)) if t not in cs]
    x = M
    y = M
    # x ~ b_i for each removed edge's b_i, y ~ a_i, and x ~ y.
    A2 += [x] * (d - 1) + ca
    B2 += cb + [y] * (d - 1)
    A2.append(x)
    B2.append(y)
    return M + 1, A2, B2


def _anneal_grow(d, D, rng, deadline):
    """Find the largest d-regular bipartite graph with diameter <= D it can reach. Returns (M, A, B) or None."""
    moore = lib.moore_bound(d, D)
    M = max(d + 1, min(450, moore // 4))

    ok = False
    A = B = None
    for _ in range(3):
        if time.monotonic() > deadline:
            return None
        shifts = rng.sample(range(M), d)
        A = [a for a in range(M) for _ in range(d)]
        B = [(a + s) % M for a in range(M) for s in shifts]
        ok, _ = _anneal(M, d, D, A, B, rng, deadline, 3000)
        if ok:
            break
    if not ok:
        return None

    best = (M, list(A), list(B))
    while time.monotonic() < deadline and 2 * (M + 1) <= moore:
        g = _grow(M, d, A, B, rng)
        if g is None:
            break
        M2, A2, B2 = g
        success = False
        for _ in range(3):
            if time.monotonic() > deadline:
                break
            tA, tB = list(A2), list(B2)
            ok2, _ = _anneal(M2, d, D, tA, tB, rng, deadline, 400)
            if ok2:
                success = True
                A2, B2 = tA, tB
                break
        if not success:
            break
        M, A, B = M2, A2, B2
        best = (M, list(A), list(B))
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        return best

    if D >= 5 and d >= 2:
        try:
            res = _anneal_grow(d, D, rng, deadline)
        except Exception:
            res = None
        if res is not None:
            M, A, B = res
            edges = [(a, M + b) for a, b in zip(A, B)]
            consider(2 * M, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
