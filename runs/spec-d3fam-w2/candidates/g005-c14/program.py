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
# Bi-Cayley graphs over groups G of order N.
#
# S is a set of d group elements containing 1. Vertices a_x and b_y (x, y in G)
# with a_x ~ b_{x s} for s in S. The graph is d-regular and bipartite. Diameter
# <= 3 holds when S S^-1 = G (every non-identity g is a quotient s t^-1).
#
# NEW in this version: a TARGETED annealing move. Instead of replacing S[idx]
# by a random element, pick a currently uncovered group element y and an
# existing member s of S, then set the new member to x = y * s. This makes
# y*s * s^-1 = y, so the move covers y immediately. Targeted moves are
# mixed with random moves. The initial set can also come from a randomized
# greedy that adds, at each step, the element that covers the most new
# quotients.
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


def _coverage_init(N, d, Q, S):
    """Quotient counts and number of uncovered non-identity elements for S."""
    cnt = [0] * N
    for j in range(d):
        for k in range(d):
            if j != k:
                cnt[Q[S[j]][S[k]]] += 1
    unc = sum(1 for y in range(1, N) if cnt[y] == 0)
    return cnt, unc


def _greedy_seed(N, d, Q, rng):
    """Randomised greedy: grow S from {1} by adding the element covering the most new quotients."""
    S = [0]
    cnt = [0] * N
    while len(S) < d:
        best_gain = -1
        best_list = []
        for x in range(1, N):
            if x in S:
                continue
            new = set()
            for s in S:
                for y in (Q[x][s], Q[s][x]):
                    if cnt[y] == 0 and y != 0:
                        new.add(y)
            g = len(new)
            if g > best_gain:
                best_gain = g
                best_list = [x]
            elif g == best_gain:
                best_list.append(x)
        x = rng.choice(best_list)
        for s in S:
            cnt[Q[x][s]] += 1
            cnt[Q[s][x]] += 1
        S.append(x)
    return S


def _pick_uncovered(cnt, N, rng):
    """Return a random uncovered non-identity element, or None if none was found quickly."""
    for _ in range(64):
        y = rng.randrange(1, N)
        if cnt[y] == 0:
            return y
    return None


def _anneal(N, d, M, Q, rng, deadline, moves):
    """Find S of size d, containing the identity 0, with S S^-1 = G; None on failure or timeout."""
    if rng.random() < 0.5:
        S = _greedy_seed(N, d, Q, rng)
    else:
        S = [0] + rng.sample(range(1, N), d - 1)
    cnt, unc = _coverage_init(N, d, Q, S)
    if unc == 0:
        return S
    inS = set(S)
    for it in range(moves):
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        T = 0.6 * (0.02 ** (it / moves))
        idx = rng.randrange(1, d)
        old = S[idx]
        if rng.random() < 0.6:
            y = _pick_uncovered(cnt, N, rng)
            if y is None:
                x = rng.randrange(1, N)
            else:
                k = rng.randrange(d)
                x = M[y][S[k]]  # then x * S[k]^-1 = y is covered
        else:
            x = rng.randrange(1, N)
        if x == 0 or x in inS:
            continue
        delta = _delta(cnt, S, idx, old, -1, Q) + _delta(cnt, S, idx, x, 1, Q)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = x
            inS.discard(old)
            inS.add(x)
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
            continue
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
        S = _anneal(N, d, M, Q, rng, deadline, 40000)
        if S is not None:
            return S, M
    return None


def _edges_from(N, d, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

        # Bi-Cayley search over groups of order N, with targeted annealing.
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
