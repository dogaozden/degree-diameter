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


# ------------------------------------------------ group helpers

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


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _pair_update(cnt, R, e, others, sign):
    """Add (sign=+1) or remove (sign=-1) all ordered pairs involving element e."""
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
    """Generator: annealing for d elements S with S S^{-1} = G (difference cover)."""
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


def _cover_search(d, D, base_n, end, rng):
    """Two-vertex-base difference-cover lifts (order 2|G|). Returns (n, edges) or None."""
    lo = base_n // 2 + 1
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
    while active and time.monotonic() < end:
        for entry in list(active):
            if time.monotonic() >= end:
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
            if n > base_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]
    return best


# ------------------------------------------------ 2x2-base voltage lifts
#
# Base graph: A0, A1 on one side, B0, B1 on the other, with
# m = [[p, d-p], [d-p, p]] parallel darts (each with a voltage in G).
# Lift over G has order 4|G|. Left multiplication by G is an automorphism,
# so the diameter check only needs BFS (depth 3) from the four vertices
# (A_i, e) and (B_j, e). The cost is the total number of unreached vertices.

def _lift_deficit(N, mt, A, B):
    """Sum over the 4 orbit representatives of (4N - |ball of radius 3|)."""
    total = 0
    for side, idx in ((0, 0), (0, 1), (1, 0), (1, 1)):
        start = (side, idx, 0)
        seen = {start}
        frontier = [start]
        for _ in range(3):
            nxt = []
            for s, k, x in frontier:
                if s == 0:
                    row = mt[x]
                    for j, g in A[k]:
                        u = (1, j, row[g])
                        if u not in seen:
                            seen.add(u)
                            nxt.append(u)
                else:
                    row = mt[x]
                    for i, h in B[k]:
                        u = (0, i, row[h])
                        if u not in seen:
                            seen.add(u)
                            nxt.append(u)
            frontier = nxt
            if not frontier:
                break
        total += 4 * N - len(seen)
    return total


def _lift_anneal(N, mt, it, d, end, rng):
    """Random restarts of annealing over voltages. Returns (slots, volt) or None."""
    while time.monotonic() < end:
        p = rng.randint(1, d - 1)
        mp = [[p, d - p], [d - p, p]]
        slots = [(i, j) for i in range(2) for j in range(2) for _ in range(mp[i][j])]
        volt = [rng.randrange(N) for _ in slots]

        def darts_of(vt):
            A = [[], []]
            B = [[], []]
            for (i, j), g in zip(slots, vt):
                A[i].append((j, g))
                B[j].append((i, it[g]))
            return A, B

        cost = _lift_deficit(N, mt, *darts_of(volt))
        for _step in range(3000):
            if cost == 0:
                return slots, volt
            if time.monotonic() >= end:
                return None
            k = rng.randrange(len(slots))
            old = volt[k]
            volt[k] = rng.randrange(N)
            c2 = _lift_deficit(N, mt, *darts_of(volt))
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / 1.0):
                cost = c2
            else:
                volt[k] = old
        if cost == 0:
            return slots, volt
    return None


def _lift_phase(d, D, best_n, end, rng):
    """Search 4-vertex-base lifts of increasing order. Returns (n, edges) or None."""
    hi_N = lib.moore_bound(d, D) // 4
    N = best_n // 4 + 1
    best = None
    while N <= hi_N and time.monotonic() < end:
        found = None
        groups = _group_list(N, rng)
        rng.shuffle(groups)
        for order, mul, inv in groups[:3]:
            now = time.monotonic()
            if now >= end:
                break
            slice_end = now + 0.3 * (end - now)
            mt = [[mul(x, y) for y in range(N)] for x in range(N)]
            it = [inv(x) for x in range(N)]
            res = _lift_anneal(N, mt, it, d, slice_end, rng)
            if res is None:
                continue
            slots, volt = res
            darts = [(i, 2 + j, g) for (i, j), g in zip(slots, volt)]
            n, edges = lib.group_lift(4, darts, N, mul)
            if n > best_n and lib.is_valid(n, edges, d, D):
                found = (n, edges)
                break
        if found is None:
            break
        best = found
        best_n = found[0]
        N = best_n // 4 + 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e

    # Phase 1: difference-cover lifts over 2 base vertices.
    try:
        r = _cover_search(d, D, base_n, start + 0.4 * total, rng)
        if r is not None and r[0] > best_n and lib.is_valid(r[0], r[1], d, D):
            best_n, best_e = r
    except Exception:
        pass

    # Phase 2: 2x2-base voltage lifts with annealed voltages (order 4|G|).
    try:
        r = _lift_phase(d, D, best_n, deadline, rng)
        if r is not None and r[0] > best_n and lib.is_valid(r[0], r[1], d, D):
            best_n, best_e = r
    except Exception:
        pass

    return best_n, best_e
