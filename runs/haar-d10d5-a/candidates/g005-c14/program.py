"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over nonabelian groups.

CONSTRUCTION.  For a finite group G and a connection set S of d elements, the Haar graph has vertices
A_g and B_g (g in G) and edges A_g ~ B_(s*g) for s in S.  It is bipartite, d-regular, and has 2|G|
vertices.  Its diameter is at most 5 when (S^-1 S)^2 = G and (S S^-1)^2 = G.

NEW IN THIS VERSION.
  * word_cost: the exact number of group elements missed by those two squared word sets.  Cost 0 means
    the Haar graph is valid, and the cost is also a smooth guide for annealing.
  * targeted move: pick an element u not covered by (S^-1 S)^2 and replace one slot with t = s_j * u,
    so that s_j^-1 t = u holds at once.  Conjugate moves (x s x^-1) are added too.
  * candidate groups: every semidirect product Z_m x|_lam Z_k with lam != 1 (nonabelian) and order in
    a window just above the current best.  Groups are tried in increasing order, and the search moves to
    larger orders after each success.

SAFETY.  A valid Haar fallback (order 3582) is checked first.  Every found graph is checked with
lib.is_valid before it is returned.  Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- groups and graphs

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def candidate_groups(lo, hi):
    """Nonabelian Z_m x|_lam Z_k with lo <= m*k <= hi, up to two lam per (m, k), sorted by order."""
    out = []
    for k in range(2, 80):
        for m in range(max(3, -(-lo // k)), hi // k + 1):
            N = m * k
            if N < lo or N > hi:
                continue
            found = 0
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((N, m, k, lam))
                    found += 1
                    if found == 2:
                        break
    out.sort()
    return out


# ------------------------------------------------------------------------- word-covering cost

def word_cost(MT, inv, N, S):
    """Return (cost, uncovered) where cost = #elements missed by (S^-1 S)^2 plus #missed by (S S^-1)^2,
    and uncovered is the array of elements missed by (S^-1 S)^2."""
    iS = inv[S]
    P = np.unique(MT[iS[:, None], S[None, :]])          # S^-1 S (contains identity)
    Q = MT[P[:, None], P[None, :]].ravel()              # (S^-1 S)^2
    mq = np.zeros(N, dtype=bool)
    mq[Q] = True
    R = np.unique(MT[S[:, None], iS[None, :]])          # S S^-1
    U = MT[R[:, None], R[None, :]].ravel()              # (S S^-1)^2
    mu = np.zeros(N, dtype=bool)
    mu[U] = True
    cost = int(N - mq.sum()) + int(N - mu.sum())
    return cost, np.flatnonzero(~mq)


TEMP = 0.5
TRIAL_STEPS = 6000
STALL_LIMIT = 2000


def anneal(MT, inv, N, d, rng, t_end):
    """Anneal connection sets with restarts until cost 0 (returns S) or time runs out (returns None)."""
    while time.monotonic() < t_end:
        S = rng.choice(N, size=d, replace=False).astype(np.int64)
        c, unc = word_cost(MT, inv, N, S)
        best_c = c
        since = 0
        for _ in range(TRIAL_STEPS):
            if c == 0:
                return S
            if time.monotonic() >= t_end or since > STALL_LIMIT:
                break
            i = int(rng.integers(d))
            r = rng.random()
            if r < 0.4 and unc.size:
                # targeted move: make s_j^-1 t equal to an uncovered element u
                u = int(unc[int(rng.integers(unc.size))])
                t = int(MT[int(S[int(rng.integers(d))]), u])
            elif r < 0.6:
                # conjugate move: t = x s_i x^-1
                x = int(S[int(rng.integers(d))])
                t = int(MT[MT[x, S[i]], inv[x]])
            else:
                t = int(rng.integers(N))
            if t in S:
                continue
            S2 = S.copy()
            S2[i] = t
            c2, unc2 = word_cost(MT, inv, N, S2)
            delta = c2 - c
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                S, c, unc = S2, c2, unc2
                if c < best_c:
                    best_c = c
                    since = 0
                else:
                    since += 1
            else:
                since += 1
        if c == 0:
            return S
    return None


# ------------------------------------------------------------------------------- group search

def search(d, D, deadline, rng, lo, slice_s=3.0):
    """Try candidate groups of increasing order above lo.  Return a valid Haar graph or None."""
    cands = candidate_groups(lo, 2300)
    best = None
    best_order = lo - 1
    while time.monotonic() + 2.0 < deadline:
        todo = [c for c in cands if c[0] > best_order]
        if not todo:
            break
        improved = False
        for N, m, k, lam in todo:
            if time.monotonic() + 2.0 >= deadline:
                break
            t_end = min(deadline, time.monotonic() + slice_s)
            try:
                MT, inv = group_meta(m, k, lam)
            except Exception:
                continue
            S = anneal(MT, inv, N, d, rng, t_end)
            if S is None:
                continue
            g = checked(MT, S, d, D)
            if g is not None:
                best = g
                best_order = N
                improved = True
                break
        if not improved and time.monotonic() + 2.0 >= deadline:
            break
    return best


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    best_order = best[0] // 2 if best is not None else 0
    lo = max(best_order + 1, 1792)
    try:
        found = search(d, D, deadline, rng, lo)
        if found is not None:
            best = found
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
