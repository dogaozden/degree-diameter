import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 3000                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side


# ---------------------------------------------------------------- group helpers
# A voltage group is G = (a, b), meaning Z_a x Z_b with a*b = m. Elements are
# indices e = x*b + y in 0..m-1 with x in Z_a, y in Z_b. (a, b) = (m, 1) is the
# cyclic group Z_m. Non-cyclic abelian groups (gcd(a, b) > 1) give lifts that
# cyclic voltages cannot produce.

def _gadd(g, v, a, b):
    """Vectorised group addition of the array g and the scalar element v."""
    x, y = g // b, g % b
    return ((x + v // b) % a) * b + (y + v % b) % b


def _gneg(v, a, b):
    """Inverse of the scalar group element v."""
    x, y = v // b, v % b
    return ((-x) % a) * b + (-y) % b


def _groups(m):
    """Group shapes (b values) to try for order m: cyclic plus one balanced non-cyclic factor."""
    out = [1]
    for b in range(math.isqrt(m), 1, -1):
        if m % b == 0 and math.gcd(b, m // b) > 1:
            out.append(b)
            break
    return out


# ---------------------------------------------------------------- lift machinery

def _neighbors(P, Pinv, V, s, m, G):
    """Neighbour table (2sm x d) of the G-lift of a d-regular bipartite base on s+s vertices.

    Dart k joins A-vertex i to B-vertex P[k, i] with voltage V[k, i]. A-lift id = i*m+g,
    B-lift id = (s+j)*m+h. The rule is A g -> B g+v and B h -> A h-v.
    """
    a, b = G
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            v = int(V[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + _gadd(g, v, a, b)
        for j in range(s):
            i = int(Pinv[k, j])
            nv = _gneg(int(V[k, i]), a, b)
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + _gadd(g, nv, a, b)
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid.

    Group translations act transitively on each fibre, so base-vertex sources suffice.
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


def _anneal(s, m, d, D, rng, deadline, G):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m, G)
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
            cand = _neighbors(P, Pinv, V, s, m, G)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m, G)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _try(s, m, d, D, rng, deadline):
    """Try every group shape of order m. Returns (P, V, G) for the first success, or None."""
    for b in _groups(m):
        if time.monotonic() > deadline:
            break
        G = (m // b, b)
        st = _anneal(s, m, d, D, rng, deadline, G)
        if st is not None:
            return st[0], st[1], G
    return None


def _graph(s, m, P, V, d, G):
    """Materialise the lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m, G)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest order m (doubling then bisection) with a valid lift."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _try(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1], st[2])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.6 * time_limit - 1.0)

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    # Optimal D = 3 construction when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    if D < 2 or d < 1:
        return fallback

    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    candidates = []  # (n, s, m, P, V, G)
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V, G = res
            candidates.append((2 * s * m, s, m, P, V, G))

    # Validate the largest candidates first; fall back if none passes.
    candidates.sort(key=lambda c: -c[0])
    for n_c, s, m, P, V, G in candidates:
        n, e = _graph(s, m, P, V, d, G)
        if lib.is_valid(n, e, d, D):
            return n, e
    return fallback
