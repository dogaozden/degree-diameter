import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines (safe fallbacks): record AL graph, projective plane incidence,
# and K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over groups G of order N with a_x ~ b_{x s}, s in S, |S| = d,
# 1 in S. Diameter <= 3 holds iff S S^-1 = G, giving order 2N.
#
# NEW in this version: a greedy "max-coverage" seeding routine. Instead of
# starting annealing from a uniformly random S, we grow S one element at a
# time, each step choosing (among a random sample of candidates) the element
# that creates the fewest new uncovered quotients. The resulting S starts
# annealing close to a cover, and every other attempt still uses a random
# start, so the search keeps its diversity.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign>0) or remove (sign<0) the quotients created by element v against S[j], j != skip.

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


def _random_start(N, d, Q, rng):
    """S = {0} plus d-1 random distinct elements, with its coverage state."""
    cnt = [0] * N
    S = [0]
    unc = N - 1
    for x in rng.sample(range(1, N), d - 1):
        unc += _delta(cnt, S, -1, x, 1, Q)
        S.append(x)
    return S, cnt, unc


def _greedy_start(N, d, Q, rng, sample_size=160):
    """Grow S greedily: each step adds the sampled candidate creating the fewest new uncovered quotients."""
    cnt = [0] * N
    S = [0]
    unc = N - 1
    while len(S) < d:
        inS = set(S)
        pool = [x for x in range(1, N) if x not in inS]
        if len(pool) > sample_size:
            pool = rng.sample(pool, sample_size)
        best, best_c = None, None
        for x in pool:
            c = _delta(cnt, S, -1, x, 1, Q)
            _delta(cnt, S, -1, x, -1, Q)  # undo the trial addition
            if best is None or c < best_c or (c == best_c and rng.random() < 0.5):
                best, best_c = x, c
        unc += _delta(cnt, S, -1, best, 1, Q)
        S.append(best)
    return S, cnt, unc


def _anneal(N, d, Q, rng, deadline, moves, S, cnt, unc):
    """Anneal S (S[0] = identity fixed) until S S^-1 = G; None on failure or timeout."""
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
        if a == 1:
            continue  # same as cyclic
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
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
        mode = rounds % 2  # alternate greedy seeding and random seeding
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
        if mode == 0:
            S, cnt, unc = _greedy_start(N, d, Q, rng)
        else:
            S, cnt, unc = _random_start(N, d, Q, rng)
        S = _anneal(N, d, Q, rng, deadline, 30000, S, cnt, unc)
        if S is not None:
            return S, M
    return None


def _edges_from(N, d, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

        # Bi-Cayley search with greedy/random seeded annealing.
        max_N = d * (d - 1) + 1
        N = best[0] // 2 + 1
        while N <= max_N and N >= d and time.monotonic() < deadline:
            rem = deadline - time.monotonic()
            budget = 0.7 * rem
            res = _search_N(N, d, rng, time.monotonic() + budget)
            if res is None:
                break
            S, M = res
            n, e = 2 * N, _edges_from(N, d, S, M)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
