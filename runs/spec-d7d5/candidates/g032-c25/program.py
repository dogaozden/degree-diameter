import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graphs (D = 3) and Haar graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: vertex-transitive Haar-type graphs over finite groups.
#
# Group G (here Z_m x|_r Z_k, possibly abelian). Connection set S of d distinct
# elements. Vertices A_g and B_g for g in G; A_g ~ B_{g*s} for s in S.
# This graph is d-regular and bipartite. Left multiplication by G is an
# automorphism that is transitive on each side, so the diameter is at most D
# iff A_0 reaches every vertex within D steps and B_0 does too.
# Search: simulated annealing over S, with cost = number of unreached vertices.
# ----------------------------------------------------------------------------

def _table(m, k, r):
    """Multiplication table M[x, y] = x*y for Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return G, M


def _sample_group(target, rng):
    """Return (m, k, r) for a group of order m*k >= target."""
    k = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12])
    m = max(2, -(-target // k))
    r = 1
    if k > 1 and m > 2 and rng.random() < 0.7:
        cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m]
        if cands:
            r = rng.choice(cands)
    return m, k, r


def _unreached_from(M, S, Sinv, G, D, start_a):
    """Number of vertices not reached within D steps from A_0 (start_a) or B_0."""
    A = np.zeros(G, dtype=bool)
    B = np.zeros(G, dtype=bool)
    if start_a:
        A[0] = True
    else:
        B[0] = True
    for _ in range(D):
        ia = np.flatnonzero(A)
        ib = np.flatnonzero(B)
        fa = np.zeros(G, dtype=bool)  # images of A under A_g -> B_{g s}
        fb = np.zeros(G, dtype=bool)  # images of B under B_h -> A_{h s^-1}
        for s in S:
            fa[M[ia, s]] = True
        for si in Sinv:
            fb[M[ib, si]] = True
        nA = A | fb
        nB = B | fa
        if np.array_equal(nA, A) and np.array_equal(nB, B):
            break
        A, B = nA, nB
    return (G - int(A.sum())) + (G - int(B.sum()))


def _cost(M, S, inv, G, D):
    Sinv = [int(inv[s]) for s in S]
    return _unreached_from(M, S, Sinv, G, D, True) + _unreached_from(M, S, Sinv, G, D, False)


def _search(d, D, G, M, inv, rng, deadline, iters):
    """Anneal a connection set S of size d. Return S with zero cost, or None."""
    S = rng.sample(range(G), d)
    cur = _cost(M, S, inv, G, D)
    c0 = float(max(cur, 1))
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c = _cost(M, S, inv, G, D)
        temp = max(0.5, 0.05 * c0 * (1.0 - t / iters))
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            S[i] = old
    return list(S) if cur == 0 else None


def _edges(G, M, S):
    """Edges of the Haar-type graph: A_g = g, B_h = G + h, A_g ~ B_{g s}."""
    return [(g, G + int(M[g, s])) for s in S for g in range(G)]


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 6.0)
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main phase: search for vertex-transitive Haar-type graphs over groups
    # of order just above the current best half-order.
    while time.monotonic() < deadline:
        target = max(d, best[0] // 2 + 1)
        m, k, r = _sample_group(target, rng)
        G, M = _table(m, k, r)
        if G < d or 2 * G <= best[0]:
            continue
        inv = np.argmax(M == 0, axis=1)
        S = _search(d, D, G, M, inv, rng, deadline, 2500)
        if S is not None:
            consider(2 * G, _edges(G, M, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
