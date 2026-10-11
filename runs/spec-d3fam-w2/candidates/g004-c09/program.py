import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: Araujo-Pardo & Lopez record family, projective plane incidence,
# and K_{d,d} as a safe fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over groups of order N (cyclic, abelian non-cyclic
# Z_a x Z_k, and semidirect Z_a x| Z_k).
#
# Vertices a_x, b_y (x, y in G); a_x ~ b_{x s} for s in S, |S| = d, 0 in S.
# Degree is exactly d on both sides, the graph is bipartite, order 2N.
# If S S^{-1} = G, every same-side pair is at distance <= 2 and every
# cross pair at distance <= 3, so the diameter is <= 3.
#
# New helper in this version: greedy seeding. S is grown one element at a
# time, each step choosing the candidate that covers the most new quotients
# x * s^{-1}. Simulated annealing then starts from that seed (alternating with
# random starts), so restarts explore different regions of the search space.
# Non-cyclic abelian groups are included as candidate groups.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign > 0) or remove (sign < 0) the quotients created by v against S[j], j != skip.

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


def _greedy(N, d, Q, rng):
    """Grow S (containing 0) greedily: at each step add the element covering the most new quotients."""
    S = [0]
    cov = set()
    while len(S) < d:
        cands = [x for x in range(1, N) if x not in S]
        rng.shuffle(cands)
        best_x, best_gain = None, -1
        for x in cands:
            new = set()
            for b in S:
                new.add(Q[x][b])
                new.add(Q[b][x])
            gain = len(new - cov - {0})
            if gain > best_gain:
                best_gain, best_x = gain, x
        if best_x is None:
            break
        S.append(best_x)
        for b in S[:-1]:
            cov.add(Q[best_x][b])
            cov.add(Q[b][best_x])
    return S


def _anneal(N, d, Q, S0, rng, deadline, moves):
    """Find S of size d, containing 0, with S S^-1 = G, starting from S0. None on failure or timeout."""
    S = list(S0)
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
    """Candidate groups of order N: cyclic, abelian non-cyclic, and a sample of semidirect products."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a < 2:
            continue
        # Abelian non-cyclic Z_a x Z_k, each unordered pair once.
        if k <= a and math.gcd(a, k) > 1:
            cands.append(("ab", a, k))
        # Semidirect Z_a x| Z_k with nontrivial action.
        for r in range(2, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
                cands.append(("sd", a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _tables(spec, N):
    """Multiplication table M and quotient table Q[x][y] = x * y^-1 for the group named by spec."""
    if spec[0] == "cyc":
        def mul(x, y):
            return (x + y) % N

        def inv(x):
            return (-x) % N
    elif spec[0] == "ab":
        _, a, k = spec

        def mul(x, y):
            i, j = divmod(x, k)
            p, q = divmod(y, k)
            return ((i + p) % a) * k + (j + q) % k

        def inv(x):
            i, j = divmod(x, k)
            return ((-i) % a) * k + (-j) % k
    else:
        _, a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    Q = [[M[x][I[y]] for y in range(N)] for x in range(N)]
    return M, Q


def _search_N(N, d, rng, deadline, specs):
    """Search for a valid S in some group of order N before the deadline. Returns (S, M) or None."""
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
        if rounds % 2 == 1:
            S0 = _greedy(N, d, Q, rng)
        else:
            S0 = [0] + rng.sample(range(1, N), d - 1)
        S = _anneal(N, d, Q, S0, rng, deadline, 25000)
        if S is not None:
            return S, M
    return None


def _edges_from(N, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D < 3 or d < 2:
        return best

    try:
        # Known record family for d = q + 2, q a prime power.
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

        # Bi-Cayley search: try orders N above the current best, half the remaining time each.
        max_N = d * (d - 1) + 1
        N = best[0] // 2 + 1
        while N <= max_N and N >= d and time.monotonic() < deadline:
            rem = deadline - time.monotonic()
            specs = _specs(N, rng)
            res = _search_N(N, d, rng, time.monotonic() + 0.5 * rem, specs)
            if res is not None:
                S, M = res
                n, e = 2 * N, _edges_from(N, S, M)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
