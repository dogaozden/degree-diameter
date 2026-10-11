import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families (diameter 3):
#   * Araujo-Pardo & Lopez graph for d = q + 2, q a prime power.
#   * Projective plane incidence graph for the largest q + 1 <= d.
#   * K_{d,d} as a universal fallback (diameter 2).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: Haar graphs over NON-ABELIAN groups.
#
# Let G be a finite group of order N and S a subset of G with |S| = d. Build
#   a_x ~ b_{x s} for x in G, s in S.
# This is d-regular bipartite on 2N vertices. Same-side distance is 2 exactly
# when S S^{-1} = G, and then every cross pair is within distance 3 as well
# (since G S = G). So diameter 3 holds iff S S^{-1} = G, which forces
# N <= d(d-1) + 1.
#
# Groups used: semidirect products Z_m x| Z_k (r^k = 1 mod m), which include the
# cyclic group (k = 1) and direct products (r = 1). Searching a difference cover
# in a non-cyclic group is a different landscape from the cyclic search, so it
# can reach orders the cyclic search cannot.
#
# Search: simulated annealing on S (identity fixed in S, WLOG up to translation),
# minimising the number of uncovered group elements. Candidate groups of all
# orders in [lo, cap] are time-sliced round-robin; the first success at order N
# prunes all candidates of order <= N, and the search continues upward.
# ----------------------------------------------------------------------------

def _group_specs(N):
    """All (m, k, r) with m * k = N and Z_m x| Z_k well defined."""
    specs = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append((m, k, r))
    return specs


def _tables(m, k, r):
    """Multiplication and inverse tables for Z_m x| Z_k."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    return N, M, I


def _pairs(M, I, e, others):
    """Group elements e * t^{-1} and t * e^{-1} for t in others, plus e * e^{-1}."""
    g = [M[e][I[e]]]
    for t in others:
        g.append(M[e][I[t]])
        g.append(M[t][I[e]])
    return g


def _apply(cnt, gs, sign):
    """Add (sign > 0) or remove the given covers; return change in number of uncovered elements."""
    ch = 0
    for g in gs:
        if sign > 0:
            if cnt[g] == 0:
                ch -= 1
            cnt[g] += 1
        else:
            cnt[g] -= 1
            if cnt[g] == 0:
                ch += 1
    return ch


def _anneal(d, N, M, I, rng, deadline):
    """Find S in G, |S| = d, identity in S, with S S^{-1} = G. Return S or None."""
    if N < d or N - 1 > d * (d - 1) or d < 2:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cnt = [0] * N
    unc = N
    for i in range(d):
        unc += _apply(cnt, _pairs(M, I, S[i], S[:i]), +1)
    if unc == 0:
        return S

    start = time.monotonic()
    span = max(1e-6, deadline - start)
    frac = 0.0
    it = 0
    while True:
        it += 1
        if (it & 255) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = (now - start) / span
        T = 0.7 * (0.02 ** frac)
        idx = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[idx]
        others = S[:idx] + S[idx + 1:]
        ch = _apply(cnt, _pairs(M, I, old, others), -1)
        ch += _apply(cnt, _pairs(M, I, x, others), +1)
        if ch <= 0 or rng.random() < math.exp(-ch / T):
            S[idx] = x
            unc += ch
            if unc == 0:
                return S
        else:
            _apply(cnt, _pairs(M, I, x, others), -1)
            _apply(cnt, _pairs(M, I, old, others), +1)


def _group_search(d, lo, cap, deadline, rng):
    """Round-robin annealing over all candidate groups of order in [lo, cap].

    Returns (N, M, S) for the largest order found, or None.
    """
    cands = []
    for N in range(lo, cap + 1):
        for spec in _group_specs(N):
            cands.append([N, spec, None])
    best = None
    slice_t = 0.25
    while cands and time.monotonic() < deadline:
        cands = [c for c in cands if best is None or c[0] > best[0]]
        if not cands:
            break
        for c in list(cands):
            if time.monotonic() >= deadline:
                break
            if best is not None and c[0] <= best[0]:
                continue
            if c[2] is None:
                c[2] = _tables(*c[1])
            N, M, I = c[2]
            S = _anneal(d, N, M, I, rng, min(deadline, time.monotonic() + slice_t))
            if S is not None:
                best = (N, M, S)
                if N == cap:
                    return best
        slice_t = min(slice_t * 1.3, 5.0)
    return best


def _haar_from_group(N, M, S):
    """Bipartite Haar-type graph: a_x (= x) ~ b_{x s} (= N + x s) for s in S."""
    edges = []
    for x in range(N):
        for s in S:
            edges.append((x, N + M[x][s]))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        # Known record family for d = q + 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # New search: Haar graphs over non-abelian groups with S S^{-1} = G.
        if d >= 2:
            cap = d * (d - 1) + 1
            lo = max(2, best[0] // 2 + 1)  # only orders that improve 2N > best
            if lo <= cap and time.monotonic() < deadline:
                res = _group_search(d, lo, cap, deadline, rng)
                if res is not None:
                    N, M, S = res
                    n, e = _haar_from_group(N, M, S)
                    consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
