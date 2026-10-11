import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# 1. Baselines: K_{d,d} (diameter 2), the projective-plane incidence graph when
#    d-1 is a prime power (Moore-optimal for D=3), and the Araujo-Pardo & Lopez
#    record family for d = q+2.
#
# 2. Bi-Cayley search (from the non-abelian parent): for a group G of order N and
#    S subset of G with |S| = d and 0 (identity) in S, let a_x ~ b_{x s} for s in S.
#    Every vertex has degree d and the graph is bipartite. Diameter <= 3 holds
#    when S S^-1 = G, which gives order 2N with N <= d(d-1)+1.
#
# 3. Search: for N ascending from the smallest value that can beat the current
#    best, look for S by simulated annealing over cyclic and semidirect products
#    Z_a x| Z_k (from the cyclic parent's group list). Each success is verified
#    with lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------


def _fallback(d, D):
    """Verified baseline: K_{d,d} for D >= 2, a single edge for D = 1."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign>0) or remove (sign<0) the quotients created by v against S[j], j != skip.

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
    """Candidate groups of order N: the cyclic group plus a sample of semidirect products Z_a x| Z_k."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                cands.append((a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _tables(spec, N):
    """Multiplication table M and quotient table Q[x][y] = x * y^-1 for the group named by spec."""
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
        S = _anneal(N, d, Q, rng, deadline, 30000)
        if S is not None:
            return S, M
    return None


def _edges_from(N, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S. Each vertex has degree |S|."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    try:
        # Moore-extremal case: incidence graph of PG(2, d-1). Optimal, so return.
        if lib.is_prime_power(d - 1):
            n_pg, e_pg = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n_pg, e_pg, d, D):
                return n_pg, e_pg

        # Araujo-Pardo & Lopez record family for d = q + 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                if n_a > best[0] and lib.is_valid(n_a, e_a, d, D):
                    best = (n_a, e_a)
            except Exception:
                pass

        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

        # Bi-Cayley search over groups of order N, ascending from the smallest N
        # that can beat the current best. Smaller N is easier, so failure at N
        # means larger N is unlikely in the remaining time.
        max_N = d * (d - 1) + 1
        N = max(d, best[0] // 2 + 1)
        while N <= max_N and time.monotonic() < deadline:
            rem = deadline - time.monotonic()
            budget = 0.5 * rem
            res = _search_N(N, d, rng, time.monotonic() + budget)
            if res is None:
                break
            S, M = res
            n, e = 2 * N, _edges_from(N, S, M)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
