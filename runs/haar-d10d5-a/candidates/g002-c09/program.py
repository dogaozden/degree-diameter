"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over metacyclic groups.

CONSTRUCTION.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A) and (g, B)
for g in G, with (g, A) ~ (s*g, B) for s in S. It is bipartite and d-regular on 2|G| vertices. It has diameter
at most 5 whenever (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  The cost of S is the number of uncovered elements in those two squared sets. Each group is a
metacyclic group Z_p x| Z_k with k | p-1, so it is nonabelian for k >= 2. Groups with order just above 1792
(the current fallback order 3582 = 2 * 1791) are tried in ascending order. Each gets a short simulated
annealing run that replaces one slot of S at a time, takes the best of several proposals, and restarts when
stalled. Any S with cost 0 is verified with lib.is_valid before it is accepted.

SAFETY.  The verified Haar fallback (order 3582) is always the starting point. Only graphs that pass
lib.is_valid are returned. Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- small valid graphs

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


# ------------------------------------------------------------------------- group candidates

def _primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]


def _primitive_root(p):
    """A primitive root mod an odd prime p."""
    fac = []
    x, q = p - 1, 2
    while q * q <= x:
        if x % q == 0:
            fac.append(q)
            while x % q == 0:
                x //= q
        q += 1
    if x > 1:
        fac.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    return None


def metacyclic_candidates(lo, hi):
    """(N, p, k, lam) for groups Z_p x|_lam Z_k with lo <= p*k <= hi, k | p-1, lam of order k. Sorted by N."""
    out = []
    for p in _primes_upto(hi):
        if p < 3:
            continue
        g = _primitive_root(p)
        if g is None:
            continue
        for k in range(2, hi // p + 1):
            N = p * k
            if N < lo or N > hi or (p - 1) % k:
                continue
            lam = pow(g, (p - 1) // k, p)
            out.append((N, p, k, lam))
    out.sort()
    return out


# ------------------------------------------------------------------------ annealing over S

def anneal(MT, inv, N, d, deadline, rng):
    """Search for S of size d with zero cost. Returns S (numpy array) or None at the deadline."""

    def cost(S):
        Si = inv[S]
        tot = 0
        for D in (np.unique(MT[np.ix_(Si, S)]), np.unique(MT[np.ix_(S, Si)])):
            P = MT[np.ix_(D, D)].ravel()
            tot += N - int(np.count_nonzero(np.bincount(P, minlength=N)))
        return tot

    def fresh():
        return rng.choice(N, size=d, replace=False).astype(np.int64)

    S = fresh()
    cur = cost(S)
    best_c = cur
    stall = 0
    T = 0.6
    K = 8
    while time.monotonic() < deadline:
        if cur == 0:
            return S
        cand, cc = None, None
        for _ in range(K):
            i = int(rng.integers(d))
            x = int(rng.integers(N))
            if np.any(S == x):
                continue
            S2 = S.copy()
            S2[i] = x
            c = cost(S2)
            if cc is None or c < cc:
                cc, cand = c, S2
        if cand is None:
            continue
        if cc == 0:
            return cand
        delta = cc - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, cur = cand, cc
        if cur < best_c:
            best_c = cur
            stall = 0
        else:
            stall += 1
        if stall > 4000:
            S = fresh()
            cur = cost(S)
            best_c = cur
            stall = 0
    return None


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)
SLICE = 4.0          # seconds of annealing per group per pass
LO_N, HI_N = 1792, 2300  # group orders to try (2N vertices; 1792 already beats the fallback)

# Valid smaller Haar graph (order 3582), checked at run time; baseline if the search fails.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    deadline = t0 + max(5.0, min(0.72 * time_limit, time_limit - 14.0))
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    best_N = best[0] // 2 if best is not None else 0
    try:
        cands = metacyclic_candidates(LO_N, HI_N)
        while time.monotonic() < deadline - 2.0:
            pool = [c for c in cands if c[0] > best_N]
            if not pool:
                break
            for N, p, k, lam in pool:
                if time.monotonic() >= deadline - 2.0:
                    break
                if N <= best_N:
                    continue
                MT, inv = group_meta(p, k, lam)
                slice_end = min(deadline, time.monotonic() + SLICE)
                S = anneal(MT, inv, N, d, slice_end, rng)
                if S is None:
                    continue
                res = checked(MT, S, d, D)
                if res is not None:
                    best = res
                    best_N = N
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
