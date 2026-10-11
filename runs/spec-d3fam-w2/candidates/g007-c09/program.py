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
    """Candidate groups of order N: cyclic first, then semidirect Z_m x| Z_k."""
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


# ---------------------------------------------- family A: 2-vertex difference covers

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


def _cover_gen(N, mul, inv, d, rng):
    """Annealing for S (size d) with S S^{-1} = G; yields None periodically, then S."""
    R = _ratio_table(N, mul, inv)
    while True:
        S = rng.sample(range(N), d)
        inS = set(S)
        cnt = [0] * N
        for a in S:
            for b in S:
                cnt[R[a][b]] += 1
        cost = cnt.count(0)
        zeros = cost
        T = 0.5
        for step in range(100000):
            if cost == 0:
                break
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
            T = max(0.05, T * 0.9999)
        if cost == 0:
            yield list(S)
            return


# ------------------------------------- family B: 4-vertex (2+2) group lifts

def _lift_cost(N, mt, blocks):
    """Number of ordered pairs at distance > 3 in the lift defined by blocks."""
    V = 4 * N
    adj = [[] for _ in range(V)]
    for (i, j), S in blocks.items():
        off_b = (2 + j) * N
        for s in S:
            for x in range(N):
                a = i * N + x
                b = off_b + mt[x][s]
                adj[a].append(b)
                adj[b].append(a)
    reach = [1 << v for v in range(V)]
    for _ in range(3):
        new = []
        for v in range(V):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(V - r.bit_count() for r in reach)


def _lift_gen(N, mul, d, k, rng):
    """Annealing over voltage blocks of a 2+2 base; yields None each step, then blocks."""
    mt = [[mul(x, s) for s in range(N)] for x in range(N)]
    sizes = {(0, 0): k, (1, 1): k, (0, 1): d - k, (1, 0): d - k}
    keys = [key for key, sz in sizes.items() if sz > 0]
    while True:
        blocks = {key: rng.sample(range(N), sizes[key]) for key in keys}
        cost = _lift_cost(N, mt, blocks)
        T = 1.0
        for _ in range(20000):
            if cost == 0:
                yield blocks
                return
            yield None
            key = keys[rng.randrange(len(keys))]
            S = blocks[key]
            i = rng.randrange(len(S))
            x = rng.randrange(N)
            if x in S:
                continue
            old = S[i]
            S[i] = x
            new_cost = _lift_cost(N, mt, blocks)
            if new_cost <= cost or rng.random() < math.exp(-(new_cost - cost) / T):
                cost = new_cost
            else:
                S[i] = old
            T = max(0.2, T * 0.9995)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e
    best_val = base_n
    moore = lib.moore_bound(d, 3)

    # Each task: [order, kind, N, mul, gen]
    tasks = []

    # Family A: difference covers, order 2N
    lo = best_val // 2 + 1
    hi = d * (d - 1) + 1
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _o, mul, inv in _group_list(N, rng)[:3]:
            tasks.append([2 * N, "cover", N, mul,
                          _cover_gen(N, mul, inv, d, rng)])

    # Family B: 2+2 base lifts, order 4N
    Nmax = moore // 4
    Nlo = best_val // 4 + 1
    for N in range(Nmax, Nlo - 1, -1):
        if N < d:
            continue
        groups = _group_list(N, rng)[:2]
        for _o, mul, _inv in groups:
            for k in (d // 2, d // 2 + 1):
                if 0 <= k <= d:
                    tasks.append([4 * N, "lift", N, mul,
                                  _lift_gen(N, mul, d, k, rng)])

    # Prefer the highest-order tasks first in the round robin.
    tasks.sort(key=lambda t: -t[0])

    while tasks and time.monotonic() < deadline:
        for entry in list(tasks):
            if time.monotonic() >= deadline:
                break
            order, kind, N, mul, gen = entry
            if order <= best_val:
                tasks.remove(entry)
                continue
            try:
                res = next(gen)
            except StopIteration:
                tasks.remove(entry)
                continue
            if res is None:
                continue
            tasks.remove(entry)
            if kind == "cover":
                n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
            else:
                darts = [(i, 2 + j, s) for (i, j), S in res.items() for s in S]
                n, edges = lib.group_lift(4, darts, N, mul)
            if n > best_val and lib.is_valid(n, edges, d, D):
                best_val = n
                best_n, best_e = n, edges
        tasks = [t for t in tasks if t[0] > best_val]

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
