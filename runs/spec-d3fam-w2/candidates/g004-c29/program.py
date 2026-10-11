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


# ------------------------------------------------ groups

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


# ------------------------------------------------ 2-block difference covers

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
    """Generator: find d elements S with S S^{-1} = G (order 2N bipartite lift)."""
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


# ------------------------------------------------ NEW: 2x2 bi-Cayley lifts

# Base multigraph: A0, A1 (ids 0, 1) and B0, B1 (ids 2, 3). Dart (i, j, g) joins
# block A_i to block B_j with voltage g. Row and column sums are d, with
# multiplicities M = [[p, d-p], [d-p, p]]. The group G acts on the left,
# which is an automorphism of the lift. So a diameter-3 check needs only 4
# BFS runs, one from each block's identity vertex. The cost is the number of
# unreached (representative, vertex) pairs, and annealing drives it to zero.

def _adj4(N, rm, darts):
    adj = [[] for _ in range(4 * N)]
    for i, j, g in darts:
        ao, bo = i * N, (2 + j) * N
        row = rm[g]
        for x in range(N):
            y = bo + row[x]
            a = ao + x
            adj[a].append(y)
            adj[y].append(a)
    return adj


def _deficit(adj, reps, n):
    """Total number of (representative, vertex) pairs at distance > 3."""
    tot = 0
    for r in reps:
        seen = bytearray(n)
        seen[r] = 1
        frontier = [r]
        cnt = 1
        for _ in range(3):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        tot += n - cnt
    return tot


def _anneal4(N, mul, rng, d):
    """Generator: anneal voltages of a 2x2 bi-Cayley lift of order 4N."""
    rm = [[mul(x, g) for x in range(N)] for g in range(N)]
    reps = (0, N, 2 * N, 3 * N)
    n = 4 * N
    while True:
        p = rng.randint(1, d - 1)
        M = ((p, d - p), (d - p, p))
        darts = []
        for i in (0, 1):
            for j in (0, 1):
                for g in rng.sample(range(N), M[i][j]):
                    darts.append([i, j, g])
        cost = _deficit(_adj4(N, rm, darts), reps, n)
        for step in range(40000):
            if cost == 0:
                break
            if step % 20 == 0:
                yield None
            k = rng.randrange(len(darts))
            i, j, old = darts[k]
            cand = rng.randrange(N)
            if any(a == i and b == j and g == cand for a, b, g in darts):
                continue
            darts[k][2] = cand
            new = _deficit(_adj4(N, rm, darts), reps, n)
            if new <= cost or rng.random() < math.exp(-(new - cost)):
                cost = new
            else:
                darts[k][2] = old
        if cost == 0:
            yield [list(t) for t in darts]
            return


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best = base_n, (base_n, base_e)
    moore = lib.moore_bound(d, D)

    # Entries: [kind, N, mul, generator, size]. Kind '4' is the new 2x2 lift,
    # kind '2' is the 2-block difference cover from the parent.
    active = []
    for N in range(moore // 4, best_n // 4, -1):
        if N < d:
            continue
        for _o, mul, _inv in _group_list(N, rng)[:6]:
            active.append(['4', N, mul, _anneal4(N, mul, rng, d), 4 * N])

    lo2 = best_n // 2 + 1
    hi2 = d * (d - 1) + 1
    for N in range(hi2, lo2 - 1, -1):
        if N < d:
            continue
        for _o, mul, inv in _group_list(N, rng)[:3]:
            active.append(['2', N, mul, _anneal(N, mul, inv, d, rng), 2 * N])

    active = [e for e in active if e[4] > best_n]

    while active and time.monotonic() < deadline:
        for entry in list(active):
            if time.monotonic() >= deadline:
                break
            kind, N, mul, gen, size = entry
            if size <= best_n:
                active.remove(entry)
                continue
            try:
                res = next(gen)
            except StopIteration:
                active.remove(entry)
                continue
            if res is None:
                continue
            active.remove(entry)
            if kind == '4':
                n, edges = lib.group_lift(
                    4, [(i, 2 + j, g) for i, j, g in res], N, mul)
            else:
                n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n = n
                best = (n, edges)
                active = [e for e in active if e[4] > best_n]
                break
        active = [e for e in active if e[4] > best_n]

    return best

