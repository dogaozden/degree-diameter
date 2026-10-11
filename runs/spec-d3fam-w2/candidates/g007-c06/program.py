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


# ------------------------------------------------ Cayley-type cover search (k = 1)
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Diameter <= 3 holds when S S^{-1} = G.

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
    """Add (sign=+1) or remove (sign=-1) all ordered pairs involving element e.

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
    """Generator: incremental annealing for d elements S with S S^{-1} = G."""
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


def _cover_gen(N, mul, inv, d, rng):
    """Generator yielding None or a finished (n, edges) lift of 2 base vertices."""
    for res in _anneal(N, mul, inv, d, rng):
        if res is None:
            yield None
        else:
            yield lib.group_lift(2, [(0, 1, g) for g in res], N, mul)


# ------------------------------------------- NEW: k-orbit voltage lifts
#
# Idea: take a random d-regular bipartite multigraph B on k "A" base vertices
# and k "B" base vertices (k = 2 or 3), give every dart a voltage in a group G
# of order N, and lift. The result has 2kN vertices, is bipartite, and has
# max degree d. We anneal the voltages so that the number of vertex pairs at
# distance > 3 (lib.bad_pairs) drops to zero. This generalises the single-orbit
# difference-cover search (k = 1) and allows orders beyond 2|G| with |G| <= d(d-1)+1.

def _base_darts(k, d, rng):
    """Random d-regular bipartite multigraph: A-vertices 0..k-1, B-vertices k..2k-1."""
    L = [j for j in range(k) for _ in range(d)]
    rng.shuffle(L)
    darts = []
    for i in range(k):
        for j in L[i * d:(i + 1) * d]:
            darts.append((i, k + j))
    return darts


def _lift_gen(k, d, N, mul, rng):
    """Generator: None per step, then one finished (n, edges) lift when bad pairs reach 0."""
    while True:
        darts = _base_darts(k, d, rng)
        volt = [rng.randrange(N) for _ in darts]

        def edges_of(v):
            return lib.group_lift(2 * k, [(a, b, g) for (a, b), g in zip(darts, v)], N, mul)

        cur = edges_of(volt)
        cost = lib.bad_pairs(cur[0], cur[1], 3)
        T = 1.0
        for _step in range(4000):
            if cost == 0:
                break
            yield None
            i = rng.randrange(len(volt))
            g = rng.randrange(N)
            if g == volt[i]:
                continue
            old = volt[i]
            volt[i] = g
            cand = edges_of(volt)
            c = lib.bad_pairs(cand[0], cand[1], 3)
            if c <= cost or rng.random() < math.exp(-(c - cost) / T):
                cost, cur = c, cand
            else:
                volt[i] = old
            T = max(0.2, T * 0.998)
        if cost == 0:
            yield cur
            return


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    cap = lib.moore_bound(d, D)
    best_n, best = base_n, (base_n, base_e)

    # active entries: [order, generator]
    active = []

    # k = 1 difference covers (order 2|G|).
    lo = base_n // 2 + 1
    hi = min(d * (d - 1) + 1, cap // 2)
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            active.append([2 * N, _cover_gen(N, mul, inv, d, rng)])

    # k = 2 and k = 3 multi-orbit voltage lifts (new).
    for k in (2, 3):
        Nmin = (base_n + 1 + 2 * k - 1) // (2 * k)
        Nmax = cap // (2 * k)
        for N in range(Nmax, Nmin - 1, -1):
            if N < d:
                continue
            for _order, mul, inv in _group_list(N, rng)[:3]:
                active.append([2 * k * N, _lift_gen(k, d, N, mul, rng)])

    while active and time.monotonic() < deadline:
        for entry in list(active):
            if time.monotonic() >= deadline:
                break
            if entry[0] <= best_n:
                active = [e for e in active if e is not entry]
                continue
            try:
                res = next(entry[1])
            except StopIteration:
                active = [e for e in active if e is not entry]
                continue
            if res is None:
                continue
            n, edges = res
            active = [e for e in active if e is not entry]
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n, best = n, (n, edges)
                active = [e for e in active if e[0] > best_n]
                break
        active = [e for e in active if e[0] > best_n]

    return best

