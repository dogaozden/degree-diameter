import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count (keeps is_valid and memory manageable)
ITERS = 6000                  # annealing iterations per attempt
RETRIES = 2                   # annealing attempts per candidate lift size
GQ_Q_MAX = 8                  # largest q for which W(q) is built (keeps construction fast)


def _largest_pp(hi):
    """Largest prime power q with 2 <= q <= hi, or None."""
    for q in range(hi, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# ---------------------------------------------------------------- D = 4 : generalized quadrangle

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1). Points are 0..P-1, lines P..2P-1.
    """
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


# ---------------------------------------------------------------- lifts (annealing)

def _s_values(D):
    """Base sizes (vertices per side) to try for voltage lifts."""
    return (1, 2, 3, 4, 6, 8) if D >= 5 else (1, 2, 3, 4, 6)


def _neighbors(P, Pinv, V, s, m):
    """Neighbour table (n x d) of the Z_m lift of a d-regular bipartite base on s+s vertices.

    Dart k joins A-vertex i to B-vertex P[k, i] with voltage V[k, i]. A-lift id = i*m+g,
    B-lift id = (s+j)*m+h. Every lift vertex gets exactly one neighbour per dart.
    """
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + (g + int(V[k, i])) % m
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + (g - int(V[k, i])) % m
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid.

    The Z_m action is transitive on each fibre, so checking base-vertex sources suffices.
    """
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal(s, m, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(m)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, m, P, V, d):
    """Materialise the lift as (n, edges), deduplicated. Side A is vertices 0..s*m-1."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _try_size(s, m, d, D, rng, deadline):
    """Attempt to anneal a valid lift of size m, with a few independent restarts."""
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, m, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _search_up(s, d, D, rng, deadline, cap, m0):
    """Starting from size m0, grow m by doubling and bisect to the largest feasible m.

    Returns (m, P, V) for the largest valid lift found, or None if m0 itself fails.
    """
    best = None
    lo, hi = 0, None
    m = max(1, m0)
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            if lo == 0:
                return best
            hi = m if hi is None else min(hi, m)
        else:
            st = _try_size(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                if lo == 0:
                    return None
                hi = m if hi is None else min(hi, m)
        if hi is None:
            m = 2 * lo
        elif hi - lo <= 1:
            break
        else:
            m = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.75 * time_limit - 1.0)

    # Trivial cases.
    if d < 1 or D < 1:
        return (1, [])
    if d == 1 or D == 1:
        return (2, [(0, 1)])

    # Fallback: K_{d,d}, diameter 2, always valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3: projective plane PG(2, q), q the largest prime power <= d - 1.
    # When d - 1 is a prime power this is Moore-optimal, so stop early.
    if D == 3:
        q = _largest_pp(d - 1)
        if q is not None:
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)
            if q == d - 1:
                return best

    # D >= 4: generalized quadrangle W(q), diameter 4 <= D.
    if D >= 4:
        q = _largest_pp(min(d - 1, GQ_Q_MAX))
        if q is not None:
            n, e = _gq_w(q)
            consider(n, e)
            if D == 4 and q == d - 1:
                return best

    # Voltage-lift annealing: random base size, starting just above the current best order.
    cap = min(N_CAP, lib._moore_bound(d, D))
    rng = random.Random(seed)
    svals = _s_values(D)
    while time.monotonic() < deadline and best[0] < cap:
        now = time.monotonic()
        s = rng.choice(svals)
        m0 = best[0] // (2 * s) + 1
        slice_end = min(deadline, now + max(1.0, (deadline - now) / 3.0))
        res = _search_up(s, d, D, rng, slice_end, cap, m0)
        if res is not None:
            m, P, V = res
            n, e = _graph(s, m, P, V, d)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
