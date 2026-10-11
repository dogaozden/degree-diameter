import itertools
import math
import random
import time

import numpy as np

import lib


_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Structured baselines (kept as safe fallbacks for D = 3 and D = 4).
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
# Bitset diameter cost on a d-regular bipartite graph stored as nbr (N x d).
# Vertices 0..N-1; color 0 = A side, color 1 = B side.
# ----------------------------------------------------------------------------

def _reach_cost(nbr, D):
    """Return (ordered pairs at distance > D, array of vertices that are not yet within D of all)."""
    N = nbr.shape[0]
    W = (N + 63) // 64
    reach = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N, dtype=np.int64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        grown = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
        if np.array_equal(grown, reach):
            break
        reach = grown
    counts = _POP16[reach.view(np.uint16)].sum(axis=1)
    cost = N * N - int(counts.sum())
    bad = np.flatnonzero(counts < N)
    return cost, bad


def _switch(nbr, a1, j1, a2, j2):
    """Degree-preserving 2-switch. Calling it twice with the same indices undoes it."""
    b1 = nbr[a1, j1]
    b2 = nbr[a2, j2]
    nbr[a1, j1] = b2
    nbr[a2, j2] = b1
    r = nbr[b1]
    r[np.flatnonzero(r == a1)[0]] = a2
    r = nbr[b2]
    r[np.flatnonzero(r == a2)[0]] = a1


def _insert(nbr, color, d, rng):
    """Add one B-vertex and one A-vertex via a random d-matching of edges. Returns new (nbr, color) or None."""
    N = nbr.shape[0]
    A = [a for a in range(N) if color[a] == 0]
    edges = [(a, int(nbr[a, j])) for a in A for j in range(d)]
    rng.shuffle(edges)
    usedA, usedB, match = set(), set(), []
    for a, b in edges:
        if a not in usedA and b not in usedB:
            match.append((a, b))
            usedA.add(a)
            usedB.add(b)
            if len(match) == d:
                break
    if len(match) < d:
        return None
    w = N        # B-side vertex, adjacent to all matched a's
    wp = N + 1   # A-side vertex, adjacent to all matched b's
    new = np.empty((N + 2, d), dtype=np.int64)
    new[:N] = nbr
    new[w] = [a for a, _ in match]
    new[wp] = [b for _, b in match]
    for a, b in match:
        r = new[a]
        r[np.flatnonzero(r == b)[0]] = w
        r = new[b]
        r[np.flatnonzero(r == a)[0]] = wp
    return new, list(color) + [1, 0]


def _anneal(nbr, color, d, D, rng, deadline, T0):
    """Anneal 2-switches in place to remove pairs at distance > D. True if diameter <= D was reached."""
    N = nbr.shape[0]
    A = np.array([i for i in range(N) if color[i] == 0], dtype=np.int64)
    cost, bad = _reach_cost(nbr, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.2, T0 * (1.0 - (now - t0) / span))
        if bad.size and rng.random() < 0.5:
            u = int(bad[rng.randrange(bad.size)])
            if color[u] == 0:
                a1 = u
            else:
                a1 = int(nbr[u, rng.randrange(d)])
        else:
            a1 = int(A[rng.randrange(len(A))])
        a2 = int(A[rng.randrange(len(A))])
        if a1 == a2:
            continue
        j1 = rng.randrange(d)
        j2 = rng.randrange(d)
        b1 = int(nbr[a1, j1])
        b2 = int(nbr[a2, j2])
        if b1 == b2 or (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
            continue
        _switch(nbr, a1, j1, a2, j2)
        c, nb = _reach_cost(nbr, D)
        if c <= cost or rng.random() < math.exp(-(c - cost) / T):
            cost, bad = c, nb
        else:
            _switch(nbr, a1, j1, a2, j2)
    return cost == 0


def _edges(nbr, color):
    """Return (n, edges) with A-vertices as the first endpoint of each edge."""
    N = nbr.shape[0]
    return N, [(a, int(b)) for a in range(N) if color[a] == 0 for b in nbr[a]]


def _grow(d, D, rng, deadline):
    """Grow a d-regular bipartite graph by vertex-pair insertion, repairing diameter by annealing.

    Starts from K_{d,d}. Returns the largest state that passed the diameter check, or None.
    """
    t_begin = time.monotonic()
    span = max(1.0, deadline - t_begin)
    nbr = np.empty((2 * d, d), dtype=np.int64)
    for a in range(d):
        nbr[a] = d + np.arange(d)
    for b in range(d):
        nbr[d + b] = np.arange(d)
    color = [0] * d + [1] * d

    cur, ccol = nbr, color
    last_ok = None
    batch = 1
    fails = 0
    base = max(0.5, span / 40.0)
    while time.monotonic() < deadline:
        cand, ccand = cur.copy(), ccol
        for _ in range(batch):
            ins = _insert(cand, ccand, d, rng)
            if ins is None:
                break
            cand, ccand = ins
        rem = deadline - time.monotonic()
        if rem <= 0.05:
            break
        budget = min(rem, base * (2 ** min(fails, 5)))
        ok = _anneal(cand, ccand, d, D, rng, time.monotonic() + budget, 3.0)
        if ok:
            cur, ccol = cand, ccand
            last_ok = (cur, ccol)
            fails = 0
            batch = min(batch * 2, 32)
        else:
            fails += 1
            if batch > 1:
                batch //= 2
            elif fails > 6:
                break
    if last_ok is None:
        return None
    return _edges(*last_ok)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + max(1.0, time_limit - max(4.0, 0.1 * time_limit))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d <= 2:
        if d == 2:
            L = 2 * D
            consider(L, [(i, (i + 1) % L) for i in range(L)])
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
            if lib.is_prime_power(d - 1):
                return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(*gq)
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if time.monotonic() < hard_end - 0.5:
        try:
            res = _grow(d, D, rng, hard_end)
        except Exception:
            res = None
        if res is not None:
            consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
