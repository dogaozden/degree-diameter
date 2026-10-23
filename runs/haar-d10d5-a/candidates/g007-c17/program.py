"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over non-abelian groups.

CONSTRUCTION.  For a finite group G with multiplication table MT and a connection set S of d elements, the
Haar graph has vertices (g, A) and (g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is
bipartite and d-regular on 2|G| vertices.  Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  The cost of S is the number of group elements missed by those two squared sets.  Simulated
annealing replaces one element of S per step, with a Metropolis acceptance rule and a geometric cooling
schedule.  Restarts use fresh random sets.  The groups are Z_m x|_lam Z_k with lam nontrivial, so they are
non-abelian, and their order is just above 2000 so the graph beats the record of 4000 vertices.

SAFETY.  The valid Haar fallback (order 3582) is checked first.  Any annealed result must pass lib.is_valid
before it replaces the fallback.  Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- groups and Haar graphs

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


# ------------------------------------------------------------------------- cost and annealing

def cost(MT, inv, S):
    """Number of group elements missed by (S^-1 S)^2 plus those missed by (S S^-1)^2.  Zero iff diameter <= 5."""
    N = MT.shape[0]
    Si = inv[S]
    P = np.unique(MT[Si[:, None], S[None, :]].ravel())   # s_i^-1 s_j
    Q = np.unique(MT[S[:, None], Si[None, :]].ravel())   # s_i s_j^-1
    c = 0
    for X in (P, Q):
        Y = MT[X[:, None], X[None, :]].ravel()
        cov = np.zeros(N, dtype=bool)
        cov[Y] = True
        c += N - int(cov.sum())
    return c


T0 = 4.0
T_MIN = 0.3
STEPS = 5000


def anneal(MT, inv, d, deadline, rng):
    """Simulated annealing over connection sets, with restarts.  Returns a zero-cost S (array) or None."""
    N = MT.shape[0]
    decay = (T_MIN / T0) ** (1.0 / STEPS)
    while time.monotonic() < deadline:
        S = rng.choice(N, size=d, replace=False).astype(np.int64)
        c = cost(MT, inv, S)
        T = T0
        for _ in range(STEPS):
            if c == 0:
                return S
            if time.monotonic() >= deadline:
                break
            i = int(rng.integers(d))
            g = int(rng.integers(N))
            if g in S:
                continue
            S2 = S.copy()
            S2[i] = g
            c2 = cost(MT, inv, S2)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                S, c = S2, c2
            T = max(T_MIN, T * decay)
        if c == 0:
            return S
    return None


def candidate_groups(N_lo=2001, N_hi=2040, kmax=60, limit=6):
    """Non-abelian metacyclic groups Z_m x| Z_k with order in [N_lo, N_hi], smallest orders first."""
    out = []
    for N in range(N_lo, N_hi + 1):
        for k in range(2, min(kmax, N // 3) + 1):
            if N % k:
                continue
            m = N // k
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((m, k, lam))
    return out[:limit]


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time; baseline if the search fails.
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

    cands = candidate_groups()
    for idx, (m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now + 1.0 >= deadline:
            break
        slice_end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            S = anneal(MT, inv, d, slice_end, rng)
            if S is not None:
                res = checked(MT, sorted(int(x) for x in S), d, D)
                if res is not None and (best is None or res[0] > best[0]):
                    best = res
                    break
        except Exception:
            continue

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
