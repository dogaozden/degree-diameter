import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# New construction: simulated annealing over bipartite d-regular graphs.
#
# Representation: A = {0..h-1}, B = {h..2h-1}. There are d layers; layer l is a
# permutation P[l] with edge (i, h + P[l][i]). Every layer is a perfect matching,
# so degrees are exactly d when no edge repeats across layers. Moves are
# within-layer swaps, which keep every layer a permutation. The cost is the
# number of unreached ordered pairs within distance D, plus a penalty for
# repeated edges. Bitset reachability is computed with numpy.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)
_PEN = 20


def _sa_bipartite(h, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on 2h vertices with diameter <= D. Return (n, edges) or None."""
    n = 2 * h
    gen = np.random.default_rng(rng.randrange(1 << 32))
    P = np.empty((d, h), dtype=np.int64)
    for l in range(d):
        P[l] = gen.permutation(h)

    cnt = np.zeros((h, h), dtype=np.int64)
    rows = np.arange(h)
    for l in range(d):
        np.add.at(cnt, (rows, P[l]), 1)
    excess = [int(np.maximum(cnt - 1, 0).sum())]

    nbr = np.empty((n, d), dtype=np.int64)
    for l in range(d):
        nbr[:h, l] = h + P[l]
        nbr[h:, l] = np.argsort(P[l])

    W = (n + 63) // 64
    vid = np.arange(n)
    base = np.zeros((n, W), dtype=np.uint64)
    base[vid, vid // 64] = np.left_shift(np.ones(n, dtype=np.uint64),
                                         (vid % 64).astype(np.uint64))

    def unreached():
        reach = base.copy()
        for _ in range(D):
            new = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
            if np.array_equal(new, reach):
                break
            reach = new
        return n * n - int(_POP8[reach.view(np.uint8)].sum())

    def swap(l, i1, i2):
        """Swap the targets of positions i1, i2 in layer l. Applying it twice restores the state."""
        a = int(P[l, i1])
        b = int(P[l, i2])
        for x, y in ((i1, a), (i2, b)):
            if cnt[x, y] > 1:
                excess[0] -= 1
            cnt[x, y] -= 1
        for x, y in ((i1, b), (i2, a)):
            cnt[x, y] += 1
            if cnt[x, y] > 1:
                excess[0] += 1
        P[l, i1] = b
        P[l, i2] = a
        nbr[:h, l] = h + P[l]
        nbr[h:, l] = np.argsort(P[l])

    cur = unreached() + _PEN * excess[0]
    T0 = 3.0
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = (now - start) / span
        T = max(0.15, T0 * (1.0 - frac))
        l = rng.randrange(d)
        i1 = rng.randrange(h)
        i2 = rng.randrange(h - 1)
        if i2 >= i1:
            i2 += 1
        swap(l, i1, i2)
        new = unreached() + _PEN * excess[0]
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            swap(l, i1, i2)

    if excess[0] != 0:
        return None
    edges = []
    for i in range(h):
        for l in range(d):
            edges.append((i, h + int(P[l, i])))
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
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

    # Annealing search for a larger d-regular bipartite graph of diameter <= D.
    if d >= 3 and D >= 2:
        cap_h = 1500
        h = best_n // 2 + 1
        try:
            while (time.monotonic() < deadline - 2.0 and h <= cap_h
                   and 2 * h <= lib.moore_bound(d, D)):
                now = time.monotonic()
                remaining = deadline - now
                slice_end = now + max(3.0, 0.6 * remaining)
                res = _sa_bipartite(h, d, D, rng, min(deadline, slice_end))
                if res is not None and lib.is_valid(res[0], res[1], d, D):
                    consider(res[0], res[1])
                    h = best_n // 2 + 1
                # On failure, retry the same h with fresh randomness.
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
