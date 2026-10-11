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


# ------------------------------------------- family 1: Cayley-type group lifts
# Two base vertices with darts (a, b, s), s in S, give a_x ~ b_{x s} on G x {0,1}.
# Diameter <= 3 when S S^{-1} = G, so this is a difference-cover search.

def _group_list(N, rng):
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
        for r in rs[:6]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _pair_update(cnt, R, e, others, sign):
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
    R = _ratio_table(N, mul, inv)
    while True:
        S = rng.sample(range(N), d)
        inS = set(S)
        cnt = [0] * N
        for a in S:
            for b in S:
                cnt[R[a][b]] += 1
        zeros = cnt.count(0)
        cost = zeros
        T = 0.5
        for step in range(200000):
            if cost == 0:
                break
            if step % 2000 == 0:
                yield None
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


def _group_search(d, lo_n, hi_n, deadline, rng):
    """Return the best valid (n, edges) found with order > lo_n, or None."""
    lo = lo_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    active = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            active.append([N, mul, _anneal(N, mul, inv, d, rng)])
    best = None
    best_N = lo - 1
    while active and time.monotonic() < deadline:
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
            n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
            active.remove(entry)
            if n > lo_n and lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]
    return best


# ---------------------------- family 2: voltage lifts of 2p-vertex base graphs
# Bipartite base on p "A" and p "B" vertices, d-regular as a multigraph, with
# random Z_m voltages on darts. The lift has 2pm vertices. Voltages are improved
# by hill climbing on lib.bad_pairs (the number of pairs at distance > 3).

def _score(p, m, darts):
    n, edges = lib.voltage_lift(2 * p, darts, m)
    return lib.bad_pairs(n, edges, 3)


def _climb_lift(p, m, d, deadline, rng):
    """Try to find a lift of order 2pm with diameter <= 3. Return (n, edges) or None."""
    now = time.monotonic()
    try_end = min(deadline, now + max(1.0, 0.3 * (deadline - now)))
    while time.monotonic() < try_end:
        A = [i for i in range(p) for _ in range(d)]
        B = [p + j for j in range(p) for _ in range(d)]
        rng.shuffle(B)
        darts = [[a, b, rng.randrange(m)] for a, b in zip(A, B)]
        cur = _score(p, m, darts)
        stall = 0
        while cur > 0 and stall < 3000 and time.monotonic() < try_end:
            cand = [x[:] for x in darts]
            if rng.random() < 0.6:
                i = rng.randrange(len(cand))
                cand[i][2] = rng.randrange(m)
            else:
                i = rng.randrange(len(cand))
                j = rng.randrange(len(cand))
                cand[i][1], cand[j][1] = cand[j][1], cand[i][1]
            s = _score(p, m, cand)
            if s <= cur:
                if s < cur:
                    stall = 0
                else:
                    stall += 1
                darts, cur = cand, s
            else:
                stall += 1
        if cur == 0:
            n, edges = lib.voltage_lift(2 * p, darts, m)
            if lib.is_valid(n, edges, d, 3):
                return n, edges
    return None


def _voltage_search(d, lo_n, deadline, rng):
    best = None
    best_n = lo_n
    moore = lib.moore_bound(d, 3)
    for p in (2, 3, 4):
        m = best_n // (2 * p) + 1
        while time.monotonic() < deadline:
            if 2 * p * m > moore:
                break
            res = _climb_lift(p, m, d, deadline, rng)
            if res is None:
                break
            best = res
            best_n = res[0]
            m = max(m + 1, best_n // (2 * p) + 1)
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + budget
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Moore-extremal and small cases: the fallback is already optimal or nothing to search.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e

    # Family 1 gets the first slice of the budget.
    g = _group_search(d, best_n, d * (d - 1) + 1,
                      start + 0.35 * budget, rng)
    if g is not None and g[0] > best_n and lib.is_valid(g[0], g[1], d, D):
        best_n, best_e = g

    # Family 2 uses the rest, starting above the current best order.
    v = _voltage_search(d, best_n, deadline, rng)
    if v is not None and v[0] > best_n and lib.is_valid(v[0], v[1], d, D):
        best_n, best_e = v

    return best_n, best_e
