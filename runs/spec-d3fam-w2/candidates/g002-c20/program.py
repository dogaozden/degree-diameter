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
        return lib.haar_graph(d, range(d))          # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)  # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)    # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 exactly when
# S S^{-1} = G (same-side pairs need distance 2, opposite-side pairs then get
# distance <= 3 automatically). So the task is a "difference cover" of size d
# in a group G, which gives order 2|G| with |G| <= d(d-1)+1.

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
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _touch(R, cnt, S, i, sign):
    """Add (sign=+1) or remove (sign=-1) every ordered pair involving S[i].

    cnt[g] counts ordered pairs (a, b) in S x S with a * b^{-1} = g.
    Returns the change in the number of covered group elements.
    """
    v = S[i]
    Rv = R[v]
    ch = 0
    for j, s in enumerate(S):
        if j == i:
            gs = (Rv[v],)
        else:
            gs = (Rv[s], R[s][v])
        for g in gs:
            c = cnt[g]
            if sign > 0:
                if c == 0:
                    ch += 1
                cnt[g] = c + 1
            else:
                cnt[g] = c - 1
                if c == 1:
                    ch -= 1
    return ch


def _search_inc(N, R, d, rng, steps, deadline, T):
    """Annealing search for d distinct elements S with S S^{-1} = G.

    Keeps incremental pair counts so each move costs O(d) instead of O(d^2).
    """
    S = rng.sample(range(N), d)
    cnt = [0] * N
    for a in S:
        for b in S:
            cnt[R[a][b]] += 1
    covered = sum(1 for c in cnt if c)
    for step in range(steps):
        if covered == N:
            return S
        if (step & 255) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        ch = _touch(R, cnt, S, i, -1)
        S[i] = x
        ch += _touch(R, cnt, S, i, +1)
        if ch >= 0 or rng.random() < math.exp(ch / T):
            covered += ch
        else:
            # Revert: remove x's pairs, restore old, re-add its pairs.
            _touch(R, cnt, S, i, -1)
            S[i] = old
            _touch(R, cnt, S, i, +1)
    return S if covered == N else None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    fb = _fallback(d, D)
    base_n, base_e = fb
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return base_n, base_e

    jobs = []                     # [N, mul, inv, R-table-or-None, T]
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append([N, mul, inv, None, rng.choice((0.4, 0.6, 0.9))])

    best = None                   # (n, edges)
    best_N = lo - 1
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            N, mul, inv, R, T = job
            if N <= best_N:
                continue
            if R is None:
                R = _ratio_table(N, mul, inv)
                job[3] = R
            S = _search_inc(N, R, d, rng, 4000, deadline, T)
            if S is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            if n > base_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
                jobs = [j for j in jobs if j[0] > best_N]
                break
        jobs = [j for j in jobs if j[0] > best_N]

    if best is not None:
        return best
    return base_n, base_e
