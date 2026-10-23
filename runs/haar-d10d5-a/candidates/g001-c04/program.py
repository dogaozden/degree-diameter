"""Bipartite degree-diameter search for the d=10, D=5 target, using random bipartite regular graphs.

CONSTRUCTION.  A simple d-regular bipartite graph on k+k vertices is the union of d perfect matchings
between the two sides, built one matching at a time.  Each new permutation is repaired by random swaps
until it creates no duplicate edge.  The graph is then checked exactly with lib.is_valid.

SEARCH.  The largest valid side size k is found by growing k geometrically, then bisecting between the
last valid and first failing sizes.  Each size gets a few independent random attempts.  Random regular
graphs of this size are expected to have diameter near log_{d-1}(n), so orders above the Haar records
are plausible.  This is a different construction from the group-based Haar search.

SAFETY.  A valid Haar fallback (order 3582) is verified first.  Only graphs that pass lib.is_valid are
returned.  Other (d, D) cases return a small always-valid graph.
"""
import itertools
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


# ------------------------------------------------------------- random bipartite regular graphs

def random_bipartite(k, d, rng):
    """Simple d-regular bipartite graph on k+k vertices (A = 0..k-1, B = k..2k-1), as a union of d
    permutation matchings with repairs to avoid repeated edges.  Returns an edge list, or None on failure."""
    used = set()
    for _ in range(d):
        perm = [int(x) for x in rng.permutation(k)]
        bad = [i for i in range(k) if i * k + perm[i] in used]
        steps = 0
        while bad:
            steps += 1
            if steps > 200000:
                return None
            i = bad.pop()
            if i * k + perm[i] not in used:
                continue
            j = int(rng.integers(k))
            if j == i:
                continue
            perm[i], perm[j] = perm[j], perm[i]
            if (i * k + perm[i] in used) or (j * k + perm[j] in used):
                perm[i], perm[j] = perm[j], perm[i]
                bad.append(i)
        for i in range(k):
            used.add(i * k + perm[i])
    return [(c // k, k + c % k) for c in used]


def random_search(d, D, deadline, rng, best, lo):
    """Find a large valid random bipartite graph.  lo is the side size of `best` (already valid).
    Grows k geometrically while probes succeed, then bisects toward the first failing size."""
    hi = None
    k = max(lo + 1, 2000)
    while time.monotonic() + 1.5 < deadline:
        ok = None
        for _ in range(2):
            if time.monotonic() + 1.5 >= deadline:
                break
            e = random_bipartite(k, d, rng)
            if e is None:
                continue
            n = 2 * k
            if lib.is_valid(n, e, d, D):
                ok = (n, e)
                break
        if ok is not None:
            best = ok
            lo = k
            if hi is None:
                k = int(k * 1.08) + 1
            else:
                if hi - lo <= 1:
                    break
                k = (lo + hi) // 2
        else:
            hi = k
            if hi - lo <= 1:
                break
            k = (lo + hi) // 2
    return best


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time; baseline if the random search fails.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    lo = best[0] // 2 if best is not None else 0
    try:
        found = random_search(d, D, deadline, rng, best, lo)
        if found is not None:
            best = found
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
