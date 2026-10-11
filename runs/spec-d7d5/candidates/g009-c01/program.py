import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent for small-diameter cases).
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
# New construction: near-regular bipartite graphs found by simulated annealing
# on double edge switches. Each state is a simple d-regular bipartite graph on
# A = 0..h-1 and B = h..2h-1. The cost is the number of ordered vertex pairs
# not reached within D steps, computed with packed bitsets in numpy.
# Random d-regular graphs of this size are close to diameter D, so local
# switches can reach diameter D with fewer structural constraints than lifts.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_HAS_BITCOUNT = hasattr(np, "bitwise_count")


def _popsum(arr):
    """Total number of set bits in a uint64 array."""
    if _HAS_BITCOUNT:
        return int(np.bitwise_count(arr).sum())
    return int(_POP8[arr.view(np.uint8)].sum())


def _moore(d, D):
    """Moore-type bipartite upper bound used to size the search."""
    if d <= 1 or D <= 0:
        return 2
    return 2 * sum((d - 1) ** i for i in range(D))


def _simple_bip(h, d, rng):
    """Random simple d-regular bipartite multigraph repaired by switches. Returns (ea, eb) or None."""
    M = h * d
    ea = [i // d for i in range(M)]
    eb = [i // d for i in range(M)]
    rng.shuffle(eb)
    for _ in range(200):
        count = {}
        for e in range(M):
            k = ea[e] * h + eb[e]
            count[k] = count.get(k, 0) + 1
        bad = [e for e in range(M) if count[ea[e] * h + eb[e]] > 1]
        if not bad:
            return ea, eb
        for e in bad:
            for _ in range(200):
                f = rng.randrange(M)
                a1, b1 = ea[e], eb[e]
                a2, b2 = ea[f], eb[f]
                if a1 == a2 or b1 == b2:
                    continue
                k1 = a1 * h + b2
                k2 = a2 * h + b1
                if count.get(k1, 0) == 0 and count.get(k2, 0) == 0:
                    count[a1 * h + b1] -= 1
                    count[a2 * h + b2] -= 1
                    count[k1] = count.get(k1, 0) + 1
                    count[k2] = count.get(k2, 0) + 1
                    eb[e], eb[f] = b2, b1
                    break
    return None


def _cost(NB, N, D, d, W):
    """Ordered vertex pairs not reached within D steps (0 means diameter <= D)."""
    reach = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N, dtype=np.int64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for j in range(d):
            new |= reach[NB[:, j]]
        reach = new
    return N * N - _popsum(reach)


def _switch(e, f, ea, eb, cB, NB, h, d):
    """Double edge switch of edges e=(a1,b1) and f=(a2,b2) into (a1,b2) and (a2,b1).

    Calling it again on the same pair undoes the switch.
    """
    a1, b1 = ea[e], eb[e]
    a2, b2 = ea[f], eb[f]
    NB[a1, e % d] = h + b2
    NB[a2, f % d] = h + b1
    NB[h + b2, cB[f]] = a1
    NB[h + b1, cB[e]] = a2
    eb[e], eb[f] = b2, b1
    cB[e], cB[f] = cB[f], cB[e]


def _anneal(h, d, D, rng, deadline):
    """Anneal a simple d-regular bipartite graph on 2h vertices. Returns (n, edges) or None."""
    N = 2 * h
    W = (N + 63) // 64
    M = h * d
    res = _simple_bip(h, d, rng)
    if res is None:
        return None
    ea, eb = res

    NB = np.empty((N, d), dtype=np.int64)
    cB = [0] * M
    fill = [0] * h
    present = set()
    for e in range(M):
        a, b = ea[e], eb[e]
        NB[a, e % d] = h + b
        cB[e] = fill[b]
        NB[h + b, fill[b]] = a
        fill[b] += 1
        present.add(a * h + b)

    cur = _cost(NB, N, D, d, W)
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = (now - start) / span
        T = 0.2 + 3.0 * (1.0 - frac)
        e = rng.randrange(M)
        f = rng.randrange(M)
        a1, b1 = ea[e], eb[e]
        a2, b2 = ea[f], eb[f]
        if a1 == a2 or b1 == b2:
            continue
        k1 = a1 * h + b2
        k2 = a2 * h + b1
        if k1 in present or k2 in present:
            continue
        _switch(e, f, ea, eb, cB, NB, h, d)
        new = _cost(NB, N, D, d, W)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            present.discard(a1 * h + b1)
            present.discard(a2 * h + b2)
            present.add(k1)
            present.add(k2)
        else:
            _switch(e, f, ea, eb, cB, NB, h, d)

    edges = [(ea[e], h + eb[e]) for e in range(M)]
    return N, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best

        if D == 4 and time.monotonic() < start + 0.3 * budget:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                if d - 1 <= 9 and lib.is_prime_power(d - 1):
                    return best

        # Ladder search over the number of vertices per side.
        moore = _moore(d, D)
        h_cap = max(d, moore // 2)
        best_h = best_n // 2
        h = min(h_cap, max(d, best_h + 1, int(0.15 * moore)))
        step = max(1, h // 30)
        attempt = max(2.0, 0.3 * budget)

        while time.monotonic() < deadline - 0.5 and h <= h_cap:
            att_dead = min(deadline, time.monotonic() + attempt)
            res = _anneal(h, d, D, rng, att_dead)
            if res is not None:
                consider(res[0], res[1])
                if best_n == 2 * h:
                    best_h = h
                h = min(h_cap, h + step)
            else:
                if step > 1:
                    step //= 2
                h = min(h_cap, best_h + max(1, step))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
