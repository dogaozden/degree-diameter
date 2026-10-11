import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 12        # groups tried per bi-Cayley order N
CLIMB_ITERS = 1500     # annealing steps per (group, connection set) try
RESTARTS = 2           # random restarts of the connection set per group
ATTEMPT_SECS = 5.0     # wall-clock slice for one bi-Cayley order N
_GROUP_CACHE = {}


# ----------------------------------------------------------------------------
# D = 3 baseline: projective plane incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Groups: Z_m x|_r Z_k, with cached multiplication-by-element permutations.
#
# New helper: each right-multiplication map x -> x*g is stored as a numpy
# permutation array. A BFS level then becomes a handful of vectorised
# fancy-index ORs over boolean arrays, with both BFS sources (A_0 and B_0)
# packed as two columns, instead of Python loops over adjacency lists.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m * k = N giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group(m, k, r):
    """Cached (order, mul, invs, perm_cache) for the group Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _GROUP_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    invs = [inv(g) for g in range(order)]
    val = (order, mul, invs, {})
    if len(_GROUP_CACHE) >= 32:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[key] = val
    return val


def _perm(grp, g):
    """Permutation array x -> x*g of the group (cached per element g)."""
    order, mul, _, cache = grp
    p = cache.get(g)
    if p is None:
        p = np.fromiter((mul(x, g) for x in range(order)), dtype=np.int64, count=order)
        cache[g] = p
    return p


def _unreached(N, grp, S, D):
    """
    Pairs (source, target) not within distance D, for sources A_0 and B_0 of the
    bi-Cayley graph with A_x ~ B_{x s} for s in S. Left multiplication is an
    automorphism, so these two sources decide the diameter.

    Both sources are packed as columns of a (2N, 2) boolean frontier array.
    """
    invs = grp[2]
    tgt_b = [N + _perm(grp, g) for g in S]      # A_x -> B_{x g}
    tgt_a = [_perm(grp, invs[g]) for g in S]    # B_y -> A_{y g^-1}
    seen = np.zeros((2 * N, 2), dtype=bool)
    seen[0, 0] = True
    seen[N, 1] = True
    f = seen.copy()
    for _ in range(D):
        new = np.zeros_like(seen)
        fa = f[:N]
        fb = f[N:]
        for t in tgt_b:
            new[t] |= fa
        for t in tgt_a:
            new[t] |= fb
        new &= ~seen
        if not new.any():
            break
        seen |= new
        f = new
    return 4 * N - int(seen.sum())


def _climb(N, grp, d, D, rng, iters, deadline):
    """Anneal a connection set S (identity fixed in S) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, grp, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, grp, S2, D)
        temp = 0.3 + 1.5 * (1.0 - it / iters)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _search(N, d, D, rng, deadline):
    """Try groups of order N with restarts; return (grp, S) on success, else None."""
    if N < d:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        grp = _group(m, k, r)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                break
            S = _climb(N, grp, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                return grp, S
    return None


def _bicayley_edges(N, grp, S):
    """Edge list of the bi-Cayley graph: A_x = x, B_y = N + y, edges A_x -- B_{x s}."""
    mul = grp[1]
    return 2 * N, [(x, N + mul(x, g)) for x in range(N) for g in S]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2, meets the Moore bound for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Bi-Cayley search: aim for orders N with 2N > current best, sampling a
    # window just above the current lower bound that widens after failures
    # and collapses back after a success.
    spread = 0
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        hi = moore // 2
        if lo > hi:
            break
        N = min(hi, lo + rng.randrange(min(spread, hi - lo) + 1))
        slice_end = min(deadline, time.monotonic() + ATTEMPT_SECS)
        found = _search(N, d, D, rng, slice_end)
        if found is not None:
            grp, S = found
            consider(*_bicayley_edges(N, grp, S))
            spread = 0
        else:
            spread += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
