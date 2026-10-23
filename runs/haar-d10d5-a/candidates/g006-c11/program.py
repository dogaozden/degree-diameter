"""Bipartite degree-diameter search for the d=10, D=5 target via annealed Haar-graph covers.

CONSTRUCTION.  Haar graph H(G, S): vertices (g, A) and (g, B) for g in G, with (g, A) ~ (s*g, B) for s in S,
|S| = d.  It is bipartite, d-regular, and has 2|G| vertices.  Its diameter is at most 5 when the two
word sets P1 = {x^-1 y : x, y in S} and P2 = {x y^-1 : x, y in S} each satisfy P*P = G.  The cost of S is
the number of group elements missed by P1*P1 plus the number missed by P2*P2.  The cost is zero exactly
when the graph is valid, and lib.is_valid confirms every candidate.

NEW IDEA (not in the parent).  The parent samples random regular bipartite graphs.  This program instead
searches the connection set S of a non-abelian metacyclic group Z_m x| Z_k with simulated annealing:
  * moves: replace one element by a random group element (60%), or by a product of two current elements (40%);
  * acceptance: Metropolis on the cover cost, with random restarts after a stale period;
  * escalation: candidate groups are tried in increasing order of order N, starting at N = 2001 (so
    2N > 4000 beats the record).  After a success at N, only groups with larger N remain pending.

SAFETY.  The verified fallback (order 3582) is kept.  Every returned graph passes lib.is_valid.
Other (d, D) cases return a small always-valid graph.
"""
import math
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------- group helpers

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


# ------------------------------------------------------------------ cover cost (new routine)

def _cover_cost(MT, N, P):
    """Number of group elements NOT of the form p*q with p, q in P."""
    Q = MT[P[:, None], P[None, :]].ravel()
    seen = np.zeros(N, dtype=bool)
    seen[Q] = True
    return N - int(np.count_nonzero(seen))


def set_cost(MT, inv, S_arr, N):
    """Total uncovered count for the two diameter-5 word conditions (zero iff the Haar graph has diameter <= 5)."""
    iS = inv[S_arr]
    P1 = MT[iS[:, None], S_arr[None, :]].ravel()   # x^-1 y
    P2 = MT[S_arr[:, None], iS[None, :]].ravel()   # x y^-1
    return _cover_cost(MT, N, P1) + _cover_cost(MT, N, P2)


def anneal(MT, inv, N, d, deadline, rng, T=0.6, patience=4000):
    """Simulated annealing over d-subsets of G with restarts.  Returns a zero-cost S, or None at the deadline."""
    while time.monotonic() < deadline:
        S = [int(x) for x in rng.choice(N, size=d, replace=False)]
        cur = set_cost(MT, inv, np.array(S), N)
        best_c = cur
        stale = 0
        steps = 0
        while cur > 0:
            steps += 1
            if steps % 128 == 0 and time.monotonic() >= deadline:
                return None
            if stale > patience:
                break
            i = int(rng.integers(d))
            if rng.random() < 0.6:
                g = int(rng.integers(N))
            else:
                a, b = rng.choice(d, size=2, replace=False)
                g = int(MT[S[a], S[b]])
            if g in S:
                stale += 1
                continue
            old = S[i]
            S[i] = g
            new = set_cost(MT, inv, np.array(S), N)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
                if cur < best_c:
                    best_c = cur
                    stale = 0
                else:
                    stale += 1
            else:
                S[i] = old
                stale += 1
        if cur == 0:
            return S
    return None


# ------------------------------------------------------------------- group candidates and search

def candidate_groups(N_lo, count=60):
    """Metacyclic groups Z_m x|_lam Z_k (non-abelian, lam != 1) with order N in [N_lo, N_lo+60), sorted by N."""
    out = []
    for N in range(N_lo, N_lo + 60):
        for k in range(2, 16):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            found = 0
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((N, m, k, lam))
                    found += 1
                    if found >= 2:
                        break
    out.sort()
    return out[:count]


def search(d, D, deadline, rng, best, N_lo):
    """Round-robin annealing over candidate groups, escalating to larger N after each success."""
    pending = candidate_groups(N_lo)
    while pending and time.monotonic() + 2.0 < deadline:
        N, m, k, lam = pending.pop(0)
        try:
            MT, inv = group_meta(m, k, lam)
        except Exception:
            continue
        slot_end = min(deadline - 1.0, time.monotonic() + 8.0)
        S = anneal(MT, inv, N, d, slot_end, rng)
        if S is not None:
            n, edges = haar_edges(MT, S)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                pending = [c for c in pending if c[0] > N]
        else:
            pending.append((N, m, k, lam))
    return best


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

    try:
        found = search(d, D, deadline, rng, best, N_lo=2001)
        if found is not None:
            best = found
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
