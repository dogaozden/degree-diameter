import math
import random
import time

import lib


def _fallback(d, D):
    """Safe, verified-by-construction graphs used whenever the search fails."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))              # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)    # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)        # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Diameter <= 3 holds when
# S S^{-1} = G (same-side pairs need distance 2; opposite-side pairs then get
# distance <= 3). The order is 2|G| with |G| <= d(d-1)+1. The cyclic case is
# the Haar-graph search, so one framework covers both.

def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus a few semidirect Z_m x| Z_k."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:3]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _search(N, R, d, rng, steps, deadline):
    """Annealing search for d distinct elements S with S S^{-1} = G."""
    S = rng.sample(range(N), d)

    def uncovered(S):
        return N - len({R[a][b] for a in S for b in S})

    cost = uncovered(S)
    T = 0.6
    for _ in range(steps):
        if cost == 0:
            return S
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        new = uncovered(S)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            S[i] = old
    return S if cost == 0 else None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Moore-extremal case is already optimal; only diameter-3 is searched.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return base_n, base_e

    # jobs: [N, mul, inv, R-table-or-None], largest orders first
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append([N, mul, inv, None])

    best = None
    best_N = lo - 1
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            N, mul, inv, R = job
            if N <= best_N:
                continue
            if R is None:
                R = _ratio_table(N, mul, inv)
                job[3] = R
            S = _search(N, R, d, rng, 1500, deadline)
            if S is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            if n > base_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
                break
        jobs = [j for j in jobs if j[0] > best_N]

    if best is not None:
        return best
    return base_n, base_e
