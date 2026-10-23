"""Haar-graph search for the bipartite degree-diameter problem (d=10, D=5).

NEW IDEA (not in the parent).  A Haar graph on a group G with connection set S (|S| = d) has diameter <= 5 exactly
when (S^-1 S)^2 = G and (S S^-1)^2 = G.  The parent's search runs annealing on full BFS balls over multi-orbit lifts.
This program anneals directly on the group-word coverage of the Haar criterion:

    cost(S) = (|G| - |(S^-1 S)^2|) + (|G| - |(S S^-1)^2|),

computed with two small numpy set products (at most 91 x 91 lookups per evaluation).  That is cheap enough for
hundreds of thousands of evaluations per run.  The target is order 2N >= 4002, so N ranges over [2001, 2100] and
only non-abelian metacyclic groups Z_m x|_r Z_k (r != 1) are tried, since abelian groups waste counting words.

Any zero-cost set S is turned into a Haar graph and checked with lib.is_valid before it is accepted.  The valid
Haar graph of order 3582 from the parent is the fallback, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
N_LO, N_HI = 2001, 2100
RESTART_STEPS = 6000


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j and (a, j)(b, l) = (a + r^j b, j + l).

    Returns (MT, inv) where MT[x, y] = x*y and inv[x] = x^-1.  Element 0 is the identity.
    """
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 128
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def metacyclic_orders(lo, hi):
    """All (N, m, k, r) with N = m*k in [lo, hi], r a non-trivial action of Z_k on Z_m (r^k = 1 mod m)."""
    out = []
    for N in range(lo, hi + 1):
        for m in range(2, N):
            if N % m:
                continue
            k = N // m
            if k < 2:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    out.append((N, m, k, r))
    return out


def word_cost(S, MT, inv, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2.  Zero iff the Haar graph of S has diameter <= 5."""
    Si = inv[S]
    P1 = np.unique(MT[Si[:, None], S[None, :]])   # s^-1 s'
    P2 = np.unique(MT[S[:, None], Si[None, :]])   # s s'^-1
    c = 2 * N
    for P in (P1, P2):
        mask = np.zeros(N, dtype=bool)
        mask[MT[P[:, None], P[None, :]].ravel()] = True
        c -= int(mask.sum())
    return c


def anneal(MT, inv, N, d, rng, deadline, L):
    """Simulated annealing on distinct connection sets S; returns a zero-cost S or None."""
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    cur = word_cost(S, MT, inv, N)
    if cur == 0:
        return S
    for step in range(L):
        if step % 256 == 0 and time.monotonic() > deadline:
            return None
        i = int(rng.integers(d))
        x = int(rng.integers(N))
        if np.any(S == x):
            continue
        old = int(S[i])
        S[i] = x
        c = word_cost(S, MT, inv, N)
        temp = 0.15 + 1.0 * (1.0 - step / L)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
            if cur == 0:
                return S.copy()
        else:
            S[i] = old
    return None


def haar_from(MT, S, N):
    """Haar graph: A-vertex g is joined to B-vertex N + s*g for each s in S."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_from(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    all_cands = metacyclic_orders(N_LO, N_HI)

    def usable_now():
        return [c for c in all_cands if 2 * c[0] > best_n]

    usable = usable_now()
    while time.monotonic() < deadline and usable:
        N, m, k, r = usable[int(rng.integers(len(usable)))]
        try:
            MT, inv = group_table(m, k, r)
        except Exception:
            continue
        S = anneal(MT, inv, N, d, rng, deadline, RESTART_STEPS)
        if S is None:
            continue
        n, edges = haar_from(MT, S, N)
        try:
            ok = n > best_n and lib.is_valid(n, edges, d, D)
        except Exception:
            ok = False
        if ok:
            best_n, best_edges = n, edges
            usable = usable_now()

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
