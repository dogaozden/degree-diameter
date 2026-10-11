import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constructions:
#   1. Moore-extremal incidence graph PG(2, d-1) when d-1 is a prime power.
#   2. Araujo-Pardo & Lopez record family for d = q + 2 (q prime power).
#   3. Bi-Cayley graphs over groups of order N: vertices a_x, b_y (x, y in G),
#      a_x ~ b_{x s} for s in S, with 1 in S and S S^{-1} = G. Diameter <= 3,
#      order 2N, N <= d(d-1)+1. Found by simulated annealing over S.
#   Fallback: K_{d,d}.
# ----------------------------------------------------------------------------


def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign>0) or remove (sign<0) quotients created by v against S[j], j != skip.

    Returns the change in the number of uncovered non-identity group elements.
    """
    change = 0
    for j, b in enumerate(S):
        if j == skip:
            continue
        for y in (Q[v][b], Q[b][v]):
            if sign > 0:
                if cnt[y] == 0:
                    change -= 1
                cnt[y] += 1
            else:
                cnt[y] -= 1
                if cnt[y] == 0:
                    change += 1
    return change


def _anneal(N, d, Q, rng, deadline, moves):
    """Find S of size d, containing the identity 0, with S S^-1 = G; None on failure or timeout."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cnt = [0] * N
    unc = N - 1
    for j in range(d):
        for k in range(d):
            if j != k:
                y = Q[S[j]][S[k]]
                if cnt[y] == 0:
                    unc -= 1
                cnt[y] += 1
    if unc == 0:
        return S
    for it in range(moves):
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        T = 0.5 * (0.02 ** (it / moves))
        idx = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[idx]
        delta = _delta(cnt, S, idx, old, -1, Q) + _delta(cnt, S, idx, x, 1, Q)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _delta(cnt, S, idx, x, -1, Q)
            _delta(cnt, S, idx, old, 1, Q)
    return None


def _specs(N, rng, cap=16):
    """Candidate groups of order N: cyclic plus a random sample of semidirect products Z_a x| Z_k."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a == 1:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                cands.append((a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _tables(spec, N):
    """Multiplication table M and quotient table Q[x][y] = x * y^-1."""
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    else:
        a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    Q = [[M[x][I[y]] for y in range(N)] for x in range(N)]
    return M, Q


def _search_N(N, d, rng, deadline):
    """Search for a valid S in some group of order N before the deadline. Returns (S, M) or None."""
    specs = _specs(N, rng)
    cache = {}
    rounds = 0
    while time.monotonic() < deadline:
        spec = specs[rounds % len(specs)]
        rounds += 1
        if spec not in cache:
            try:
                cache[spec] = _tables(spec, N)
            except Exception:
                cache[spec] = None
        tab = cache[spec]
        if tab is None:
            continue
        M, Q = tab
        S = _anneal(N, d, Q, rng, deadline, 20000)
        if S is not None:
            return S, M
    return None


def _edges_from(N, d, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D < 3 or d < 3:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        # Moore-extremal case: incidence graph of PG(2, d-1).
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best

        # Araujo-Pardo & Lopez record family for d = q + 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

        # Bi-Cayley search: only N with 2N > current order can improve.
        # Scan N upward, spending a share of the remaining time on each value,
        # and keep going past failures so that no N is skipped by a stall.
        hi = d * (d - 1) + 1
        N = max(d, best[0] // 2 + 1)
        while N <= hi and time.monotonic() < deadline:
            rem = deadline - time.monotonic()
            slots = hi - N + 1
            budget = min(0.5 * rem, max(1.0, 1.5 * rem / slots))
            res = _search_N(N, d, rng, time.monotonic() + budget)
            if res is not None:
                S, M = res
                consider(2 * N, _edges_from(N, d, S, M))
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
