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


# ------------------------------------------------ Phase 1: Cayley-type covers
# Two base vertices with darts S give a_x ~ b_{x s}. Diameter <= 3 when S S^{-1} = G.

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


def _cayley_search(d, lo, hi, deadline, rng):
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
            if lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]
    return best


# ------------------------------------------- Phase 2: 2+2 base voltage lifts
# Base: A-vertices 0,1 and B-vertices 2,3. Each A has d darts, each B receives
# d darts in total (so the lift is d-regular and bipartite). The objective is
# the number of vertex pairs at distance > 3, minimised by annealing over
# group labels and B-target swaps.

def _groups(N, rng):
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k or N // k < 2:
            continue
        m = N // k
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _lift_search(N, d, D, deadline, rng):
    groups = _groups(N, rng)
    if not groups:
        return None
    while time.monotonic() < deadline:
        order, mul, _inv = rng.choice(groups)
        tgt = [0] * d + [1] * d
        rng.shuffle(tgt)
        cur = [[idx // d, 2 + tgt[idx], rng.randrange(order)] for idx in range(2 * d)]

        def score(st):
            n, e = lib.group_lift(4, st, order, mul)
            return lib.bad_pairs(n, e, D), n, e

        c, n, e = score(cur)
        T = 0.6
        stall = 0
        while stall < 4000 and time.monotonic() < deadline:
            if c == 0:
                if lib.is_valid(n, e, d, D):
                    return n, e
                break
            i = rng.randrange(2 * d)
            accepted = False
            if rng.random() < 0.5:
                old = cur[i][2]
                cur[i][2] = rng.randrange(order)
                c2, n2, e2 = score(cur)
                if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                    accepted = True
                else:
                    cur[i][2] = old
            else:
                j = rng.randrange(2 * d)
                if cur[i][1] != cur[j][1]:
                    cur[i][1], cur[j][1] = cur[j][1], cur[i][1]
                    c2, n2, e2 = score(cur)
                    if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                        accepted = True
                    else:
                        cur[i][1], cur[j][1] = cur[j][1], cur[i][1]
            if accepted:
                if c2 < c:
                    stall = 0
                else:
                    stall += 1
                c, n, e = c2, n2, e2
            else:
                stall += 1
            T = max(0.05, T * 0.9995)
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_end = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)
    try:
        # Phase 1: Cayley-type difference covers (keeps the earlier strong result).
        mid = start + 0.4 * (budget_end - start)
        lo = base_n // 2 + 1
        hi = d * (d - 1) + 1
        if lo <= hi:
            res = _cayley_search(d, lo, hi, mid, rng)
            if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res

        # Phase 2: 2+2 base lifts over groups of order N, giving 4N vertices.
        maxN = lib.moore_bound(d, D) // 4
        N = best[0] // 4 + 1
        while N <= maxN and time.monotonic() < budget_end:
            res = _lift_search(N, d, D, budget_end, rng)
            if res is None:
                break
            if res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res
            N = max(N + 1, best[0] // 4 + 1)
    except Exception:
        pass

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
