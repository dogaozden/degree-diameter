import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallbacks. Every returned graph is checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """Safe graphs used whenever the search fails or does not apply."""
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
            return lib.araujo_lopez_graph(d - 2)        # record family
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over groups G of order N.
#
# With S a subset of G of size d, the bipartite graph a_x ~ b_{x s} (s in S)
# is d-regular on 2N vertices. Its diameter is at most 3 whenever S S^{-1} = G,
# so the search is for a difference cover of size d in some group of order N.
# Since N <= d(d-1)+1, the order is at most 2(d(d-1)+1).
#
# Search: incremental simulated annealing that minimises the number of
# uncovered group elements, run round-robin over many candidate groups
# (cyclic and semidirect products Z_m x| Z_k) so no single group stalls the run.
# ----------------------------------------------------------------------------

MAX_GROUPS_PER_N = 8


def _group_list(N, rng):
    """Candidate groups of order N: the cyclic group plus some semidirect products."""
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
    rest = groups[1:]
    rng.shuffle(rest)
    return [groups[0]] + rest


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _pair_update(cnt, R, e, others, sign):
    """Add (sign=+1) or remove (sign=-1) all ordered pairs involving e.

    Returns the change in the number of zero entries of cnt.
    """
    change = 0
    row = R[e]
    gs = [row[e]] + [row[o] for o in others] + [R[o][e] for o in others]
    if sign > 0:
        for g in gs:
            if cnt[g] == 0:
                change -= 1
            cnt[g] += 1
    else:
        for g in gs:
            cnt[g] -= 1
            if cnt[g] == 0:
                change += 1
    return change


def _anneal(N, mul, inv, d, rng):
    """Generator. Yields None periodically so the driver can share time across
    groups, and yields the cover S (a list) once found. Restarts from a fresh
    random state when a run stalls.
    """
    R = _ratio_table(N, mul, inv)
    steps = 150000
    while True:
        S = rng.sample(range(N), d)
        inS = set(S)
        cnt = [0] * N
        for a in S:
            for b in S:
                cnt[R[a][b]] += 1
        zeros = cnt.count(0)
        cost = zeros
        for step in range(steps):
            if cost == 0:
                break
            if step % 2000 == 0:
                yield None
            T = 0.6 * (0.03 / 0.6) ** (step / steps)
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in inS:
                continue
            old = S[i]
            others = S[:i] + S[i + 1:]
            zeros += _pair_update(cnt, R, old, others, -1)
            zeros += _pair_update(cnt, R, x, others, 1)
            if zeros <= cost or rng.random() < math.exp(-(zeros - cost) / T):
                S[i] = x
                inS.discard(old)
                inS.add(x)
                cost = zeros
            else:
                zeros += _pair_update(cnt, R, x, others, -1)
                zeros += _pair_update(cnt, R, old, others, 1)
        if cost == 0:
            yield list(S)
            return


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.5)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Moore-extremal or outside the diameter-3 regime: nothing to search.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1           # need 2N > current best order
    hi = d * (d - 1) + 1           # hard bound for difference covers
    if lo > hi:
        return base_n, base_e

    try:
        # Active entries: [N, mul, generator]. Groups are created lazily,
        # so the expensive ratio tables are only built when a generator runs.
        active = []
        for N in range(lo, hi + 1):
            if N < d:
                continue
            for _order, mul, inv in _group_list(N, rng)[:MAX_GROUPS_PER_N]:
                active.append([N, mul, _anneal(N, mul, inv, d, rng)])

        best = None
        best_N = lo - 1
        while active and time.monotonic() < deadline:
            progressed = False
            for entry in list(active):
                if time.monotonic() >= deadline:
                    break
                N, mul, gen = entry
                if N <= best_N:
                    active.remove(entry)
                    continue
                try:
                    res = next(gen)
                except StopIteration:
                    active.remove(entry)
                    continue
                if res is None:
                    continue
                progressed = True
                active.remove(entry)
                n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
                if n > base_n and n > (best[0] if best else 0) \
                        and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = N
                    active = [e for e in active if e[0] > best_N]
                    break
            active = [e for e in active if e[0] > best_N]
            if not progressed and not active:
                break

        if best is not None and lib.is_valid(best[0], best[1], d, D):
            return best
    except Exception:
        pass

    return base_n, base_e
