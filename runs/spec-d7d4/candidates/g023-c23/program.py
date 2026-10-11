import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Group-Haar graphs.
#
# For a finite group G of order N with connection set S (|S| = d), the graph has
# vertices a_g, b_g (g in G) and edges a_g ~ b_{g*s} for s in S. It is d-regular
# and bipartite. Left multiplication by h is an automorphism (a_g -> a_{hg},
# b_g -> b_{hg}), so the diameter is at most D iff every vertex is within D of
# a_e and of b_e. Each check is a short numpy BFS on the group.
# Groups tried: cyclic Z_N and semidirect products Z_a x|_r Z_k with a*k = N.
# ----------------------------------------------------------------------------

def _group_options(N, rng):
    """Return (a, k, r) descriptors for groups of order N; (N, 1, 0) is the cyclic group."""
    opts = [(N, 1, 0)]
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                opts.append((a, k, r))
    if len(opts) > 8:
        rest = opts[1:]
        rng.shuffle(rest)
        opts = [opts[0]] + rest[:7]
    return opts


def _tables(opt, N):
    """Return (Tb, invlist): Tb[s, g] = g*s as an int array, invlist[s] = s^{-1}."""
    a, k, r = opt
    if k == 1:
        _, mul, inv = lib.cyclic_group(a)
    else:
        _, mul, inv = lib.semidirect_group(a, k, r)
    Tb = np.empty((N, N), dtype=np.int64)
    for s in range(N):
        Tb[s] = [mul(g, s) for g in range(N)]
    invlist = [inv(s) for s in range(N)]
    return Tb, invlist


def _cost(N, Tb, invlist, S, D):
    """Number of (source, vertex) pairs not reached within D steps, for sources a_e and b_e."""
    tot = 0
    for src_a in (True, False):
        A = np.zeros(N, dtype=bool)
        B = np.zeros(N, dtype=bool)
        if src_a:
            A[0] = True
        else:
            B[0] = True
        for i in range(D):
            if (i % 2 == 0) == src_a:
                nb = np.zeros(N, dtype=bool)
                for s in S:
                    nb[Tb[s]] |= A
                B |= nb
            else:
                na = np.zeros(N, dtype=bool)
                for s in S:
                    na[Tb[invlist[s]]] |= B
                A |= na
        tot += 2 * N - int(A.sum()) - int(B.sum())
    return tot


def _search(N, Tb, invlist, d, D, deadline, rng):
    """Hill-climb with restarts for a connection set S of size d with cost 0, or None."""
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        c = _cost(N, Tb, invlist, S, D)
        temp = 1.0
        for it in range(20000):
            if c == 0:
                return sorted(S)
            if it % 100 == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(d)
            y = rng.randrange(N)
            if y in S:
                continue
            S2 = S[:]
            S2[i] = y
            c2 = _cost(N, Tb, invlist, S2, D)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
                S, c = S2, c2
            temp = max(0.2, temp * 0.9995)
        if c == 0:
            return sorted(S)
    return None


def _group_search(d, D, moore, best, deadline, rng):
    """Try group orders m upward; each success raises the best and rules out smaller m."""
    lo = max(d, best[0] // 2 + 1)
    hi = moore // 2
    pending = list(range(lo, hi + 1))
    slice_len = 1.0
    while pending and time.monotonic() < deadline:
        for m in list(pending):
            now = time.monotonic()
            if now >= deadline:
                break
            if m not in pending:
                continue
            opt = rng.choice(_group_options(m, rng))
            Tb, invlist = _tables(opt, m)
            S = _search(m, Tb, invlist, d, D, min(deadline, now + slice_len), rng)
            if S is None:
                continue
            Tl = Tb.tolist()
            edges = [(g, m + Tl[s][g]) for g in range(m) for s in S]
            n = 2 * m
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                pending = [x for x in pending if x > m]
        slice_len = min(slice_len * 1.4, 10.0)
    return best


# ----------------------------------------------------------------------------
# Driver. The fallback K_{d,d} (diameter 2) is always valid for D >= 2.
# Every candidate is checked with lib.is_valid before it can replace the best.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.80 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Exact optimum for D = 3 when d - 1 is a prime power (projective plane incidence).
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        try:
            n, e = lib.projective_plane_incidence(d - 1)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass
        if best[0] >= moore:
            return best

    try:
        best = _group_search(d, D, moore, best, deadline, rng)
    except Exception:
        pass

    return best
