import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: K_{d,d} (diameter 2), the Moore-extremal projective plane incidence
# graph when d-1 is a prime power, and the Araujo-Pardo & Lopez record family
# for d = q + 2 (q a prime power).
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2), or trivial graphs for tiny parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over groups of order N (cyclic and semidirect Z_a x| Z_k).
#
# For S subset of G with |S| = d and 0 (identity) in S, let a_x ~ b_{x s} for
# s in S. Every vertex has degree d and the graph is bipartite with 2N vertices.
# If S S^{-1} = G then the diameter is at most 3, so order 2N with N <= d(d-1)+1.
#
# Search: simulated annealing over S, minimising the number of uncovered group
# elements, over several groups of order N.
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
    """Candidate groups of order N: cyclic plus a shuffled sample of semidirect products."""
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
            if all(cache.get(s) is None for s in specs if s in cache) and rounds > 4 * len(specs):
                return None
            continue
        M, Q = tab
        S = _anneal(N, d, Q, rng, deadline, 30000)
        if S is not None:
            return S, M
    return None


def _edges_from(N, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S. All edges distinct, degree d."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D < 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1), optimal, nothing to improve.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Bi-Cayley search: order 2N needs S S^{-1} = G with |S| = d.
    # Only N with 2N > best_n can improve, so search ascending from just above.
    max_N = d * (d - 1) + 1
    N = max(best_n // 2 + 1, d)
    try:
        while N <= max_N and time.monotonic() < deadline:
            rem = deadline - time.monotonic()
            budget = 0.6 * rem
            res = _search_N(N, d, rng, time.monotonic() + budget)
            if res is None:
                break
            S, M = res
            consider(2 * N, _edges_from(N, S, M))
            N = max(N + 1, best_n // 2 + 1)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
