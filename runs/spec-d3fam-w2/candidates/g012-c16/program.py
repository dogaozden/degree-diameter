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
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus semidirect Z_m x| Z_k."""
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


# ----------------------------------------------- 2-part difference cover search

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
    """Generator yielding None periodically and the cover S when found."""
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


def _diffcover_search(cur_n, d, rng, deadline):
    """Parent-style search: order 2|G| with a difference cover of size d. Returns (n, edges) or None."""
    lo = cur_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    active = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _o, mul, inv in _group_list(N, rng):
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
            if n > cur_n and lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]
    return best


# ------------------------------------- new: 4-vertex (2+2) group lift annealing

_PAIRS = [(0, 2), (0, 3), (1, 2), (1, 3)]


def _lift_darts(S):
    return [(u, v, g) for (u, v), Sk in zip(_PAIRS, S) for g in Sk]


def _lift_anneal(N, mul, d, p, rng, until):
    """Anneal a 2+2 base lift over a group of order N.

    Darts: A0-B2 with p elements, A0-B3 with d-p, A1-B2 with d-p, A1-B3 with p.
    Every base vertex then has degree d. Cost = number of pairs at distance > 3.
    Returns (n, edges) on success, or None.
    """
    sizes = [p, d - p, d - p, p]
    if max(sizes) > N:
        return None
    S = [rng.sample(range(N), s) for s in sizes]

    def cost(S):
        n, edges = lib.group_lift(4, _lift_darts(S), N, mul)
        return lib.bad_pairs(n, edges, 3)

    c = cost(S)
    T = 2.0
    while c > 0:
        if time.monotonic() >= until:
            return None
        k = rng.randrange(4)
        i = rng.randrange(sizes[k])
        g = rng.randrange(N)
        if g in S[k]:
            continue
        old = S[k][i]
        S[k][i] = g
        c2 = cost(S)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[k][i] = old
        T = max(0.1, T * 0.999)
    return lib.group_lift(4, _lift_darts(S), N, mul)


def _lift_phase(base_n, d, D, rng, end):
    """Search 2+2 lifts with 4|G| > base_n. Returns best (n, edges) or None."""
    hi = lib.moore_bound(d, D) // 4
    lo = base_n // 4 + 1
    best = None
    cur_n = base_n
    for N in range(hi, lo - 1, -1):
        if time.monotonic() >= end:
            break
        groups = _group_list(N, rng)
        rng.shuffle(groups)
        for _o, mul, _inv in groups[:2]:
            if time.monotonic() >= end:
                break
            p = rng.randrange(1, d)
            until = min(end, time.monotonic() + 2.5)
            res = _lift_anneal(N, mul, d, p, rng, until)
            if res is None:
                continue
            n, edges = res
            if n > cur_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                cur_n = n
                break
        if best is not None:
            break
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    try:
        start = time.monotonic()
        budget = max(1.0, 0.8 * time_limit - 2.0)
        deadline = start + budget
        rng = random.Random(seed)

        base_n, base_e = _fallback(d, D)
        if not lib.is_valid(base_n, base_e, d, D):
            return 1, []

        if D != 3 or d < 3 or lib.is_prime_power(d - 1):
            return base_n, base_e

        best = None
        cur_n = base_n

        # Phase 1: 2+2 lifts over groups, descending order, half the budget.
        phase1_end = start + 0.5 * budget
        res = _lift_phase(base_n, d, D, rng, phase1_end)
        if res is not None:
            best = res
            cur_n = res[0]

        # Phase 2: difference-cover search for the rest of the budget.
        dc = _diffcover_search(cur_n, d, rng, deadline)
        if dc is not None and dc[0] > cur_n and lib.is_valid(dc[0], dc[1], d, D):
            best = dc

        if best is not None and best[0] > base_n and lib.is_valid(best[0], best[1], d, D):
            return best
        return base_n, base_e
    except Exception:
        return _fallback(d, D)
