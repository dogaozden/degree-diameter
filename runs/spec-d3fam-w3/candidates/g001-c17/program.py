import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over (possibly non-abelian) groups of order M.
#
# For a group G of order M and a d-subset S of G, put a_x ~ b_{xs} for s in S.
# This is d-regular and bipartite. Distances are at most 3 when both
#   S S^{-1} = G   (a-a pairs at distance <= 2)
#   S^{-1} S = G   (b-b pairs at distance <= 2)
# hold, since then a-b pairs are at distance <= 3 (G S = G).
# Non-cyclic groups come from lib.semidirect_group(a, k, r), which covers
# cyclic (k = 1) and direct products (r = 1) as special cases.
# The search anneals S to cover G, and every graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _cost(S, mt, itb):
    """Number of uncovered elements in S S^{-1} and S^{-1} S (0 means both cover G)."""
    L = set()
    R = set()
    for a in S:
        ma = mt[a]
        ia = itb[a]
        for b in S:
            L.add(ma[itb[b]])
            R.add(mt[ia][b])
    M = len(mt)
    return 2 * M - len(L) - len(R)


def _anneal(M, d, mt, itb, rng, deadline, iters):
    """Anneal a d-subset S of the group (identity 0 included) with S S^{-1} = S^{-1} S = G. Returns S or None."""
    S = [0] + rng.sample(range(1, M), d - 1)
    cur = _cost(S, mt, itb)
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        T = 0.6 * (0.02 / 0.6) ** (it / iters)
        i = rng.randrange(1, d)
        x = rng.randrange(1, M)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c = _cost(S, mt, itb)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
        else:
            S[i] = old
    return S if cur == 0 else None


def _params(M, rng, cap=8):
    """Group parameters (a, k, r) with a*k = M: cyclic first, then a few semidirect/direct products."""
    ps = [(M, 1, 1)]
    for a in range(2, M):
        if M % a:
            continue
        k = M // a
        if k < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                ps.append((a, k, r))
    rest = ps[1:]
    rng.shuffle(rest)
    return [ps[0]] + rest[:cap]


def _tables(prm):
    """Multiplication and inverse tables for the group given by semidirect_group parameters."""
    a, k, r = prm
    M, mul, inv = lib.semidirect_group(a, k, r)
    mt = [[mul(x, y) for y in range(M)] for x in range(M)]
    itb = [inv(x) for x in range(M)]
    return mt, itb


def _bicayley_edges(M, S, mt):
    """Edges a_x ~ b_{x s} with a_x = x, b_y = M + y."""
    return [(x, M + mt[x][s]) for x in range(M) for s in S]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Moore-optimal case: PG(2, d-1) incidence graph.
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except (ValueError, StopIteration, KeyError):
            pass
        return best

    # Araujo-Pardo & Lopez record family when d-2 is a prime power.
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except (ValueError, StopIteration, KeyError):
            pass

    if d < 3:
        return best

    # Bold search: bi-Cayley graphs over non-cyclic groups, for orders above the current best half.
    lo = max(d, best_n // 2 + 1)
    hi = d * (d - 1) + 1
    M = lo
    while M <= hi and time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(0.5, 2.0 * remaining / (hi - M + 1)))
        params = _params(M, rng)
        cache = [None] * len(params)
        found = None
        while found is None and time.monotonic() < slice_end:
            for idx, prm in enumerate(params):
                if time.monotonic() >= slice_end:
                    break
                if cache[idx] is None:
                    cache[idx] = _tables(prm)
                mt, itb = cache[idx]
                S = _anneal(M, d, mt, itb, rng, slice_end, 20000)
                if S is not None:
                    found = (mt, S)
                    break
        if found is not None:
            mt, S = found
            e = _bicayley_edges(M, S, mt)
            consider(2 * M, e)
        M += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
