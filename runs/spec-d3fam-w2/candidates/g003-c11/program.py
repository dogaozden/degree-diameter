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
# Bi-Cayley graphs over groups of order N.
#
# Let G be a group of order N and S a subset of G with |S| = d and 1 in S.
# Vertices a_x and b_y (x, y in G); a_x ~ b_{x s} for s in S.
# Same-side distance 2 forces S S^-1 = G. Then cross distance is at most 3,
# so diameter <= 3 holds, giving order 2N with N <= d(d-1)+1.
#
# Two local searches over S minimise the number of uncovered group elements:
#   _anneal : simulated annealing (parent's method)
#   _tabu   : NEW. Tabu search with best-of-sample moves. Each step samples
#             several (position, element) swaps, applies the best non-tabu
#             one, and forbids re-inserting the removed element for a few
#             steps. This escapes the plateaus where annealing stalls near
#             the largest feasible N.
# The two are alternated across restarts and across random groups.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign>0) or remove (sign<0) the quotients created by element v against S[j], j != skip.

    Updates cnt in place and returns the change in the number of uncovered non-identity elements.
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


def _eval_swap(cnt, S, idx, old, x, Q):
    """Uncovered-count change if S[idx] = old is replaced by x. Leaves cnt unchanged."""
    d1 = _delta(cnt, S, idx, old, -1, Q)
    d2 = _delta(cnt, S, idx, x, 1, Q)
    _delta(cnt, S, idx, x, -1, Q)
    _delta(cnt, S, idx, old, 1, Q)
    return d1 + d2


def _init_state(N, d, Q, rng):
    """Random S of size d containing the identity, with its quotient counts."""
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
    return S, cnt, unc


def _anneal(N, d, Q, rng, deadline, moves):
    """Simulated annealing for S with S S^-1 = G; None on failure or timeout."""
    S, cnt, unc = _init_state(N, d, Q, rng)
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


def _tabu(N, d, Q, rng, deadline, steps, sample=30, tenure=7):
    """NEW: tabu search for S with S S^-1 = G; None on failure, timeout, or step exhaustion."""
    S, cnt, unc = _init_state(N, d, Q, rng)
    if unc == 0:
        return S
    tabu_until = {}  # element -> last iteration at which it may not be re-inserted
    for it in range(steps):
        if (it & 127) == 0 and time.monotonic() >= deadline:
            return None
        best = None
        for _ in range(sample):
            idx = rng.randrange(1, d)
            x = rng.randrange(1, N)
            if x in S:
                continue
            old = S[idx]
            dl = _eval_swap(cnt, S, idx, old, x, Q)
            # Aspiration: a tabu move is allowed if it finishes the cover.
            if tabu_until.get(x, -1) > it and unc + dl != 0:
                continue
            if best is None or dl < best[0] or (dl == best[0] and rng.random() < 0.5):
                best = (dl, idx, x, old)
        if best is None:
            continue
        dl, idx, x, old = best
        _delta(cnt, S, idx, old, -1, Q)
        _delta(cnt, S, idx, x, 1, Q)
        S[idx] = x
        unc += dl
        tabu_until[old] = it + tenure
        if unc == 0:
            return S
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
    """Search for a valid S in some group of order N before the deadline. Returns (S, M) or None.

    Restarts alternate between annealing and tabu search, so each random group
    gets both methods.
    """
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
        if rounds % 2 == 1:
            S = _anneal(N, d, Q, rng, deadline, 30000)
        else:
            S = _tabu(N, d, Q, rng, deadline, 3000)
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

        # Search: bi-Cayley graphs over cyclic and semidirect groups.
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
