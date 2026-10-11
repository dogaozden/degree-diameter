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
# graph on G x {0,1} with a_x ~ b_{x s}. Diameter <= 3 when S S^{-1} = G.

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


def _cayley_phase(d, lo, hi, rng, deadline):
    """Single-orbit-pair difference-cover search. Returns (n, edges) or None."""
    active = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            gen = _anneal(N, mul, inv, d, rng)
            active.append([N, mul, gen])

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


# ------------------------------------------- NEW: multi-orbit voltage lifts
#
# k orbits on each side: A_0..A_{k-1}, B_0..B_{k-1}, each a copy of a group G
# of order N. Dart counts c[i][j] form a circulant pattern with row and column
# sums d, so every vertex has degree exactly d. Voltages are found by a
# simulated-annealing search on the number of pairs at distance > 3
# (lib.bad_pairs). Order is 2kN, which can exceed the single-orbit records.

def _orbit_counts(k, d, shift):
    """k x k integer matrix with every row and column summing to d."""
    q, r = divmod(d, k)
    return [[q + (1 if (j - i - shift) % k < r else 0) for j in range(k)]
            for i in range(k)]


def _copy_sets(s):
    return [[list(x) for x in row] for row in s]


def _orbit_search(k, N, mul, d, rng, until):
    """Find voltage sets with bad_pairs == 0 for diameter 3. Returns (cnt, sets) or None."""
    cnt = _orbit_counts(k, d, rng.randrange(k))
    if max(max(row) for row in cnt) > N:
        return None
    n = 2 * k * N
    sets = [[rng.sample(range(N), cnt[i][j]) for j in range(k)] for i in range(k)]

    def cost_of(s):
        darts = [(i, k + j, g) for i in range(k) for j in range(k) for g in s[i][j]]
        _, e = lib.group_lift(2 * k, darts, N, mul)
        return lib.bad_pairs(n, e, 3)

    cur = cost_of(sets)
    best_c, best_s = cur, _copy_sets(sets)
    T = 0.4
    while cur > 0 and time.monotonic() < until:
        i = rng.randrange(k)
        j = rng.randrange(k)
        pos = rng.randrange(cnt[i][j])
        new = rng.randrange(N)
        row = sets[i][j]
        if new in row:
            continue
        old = row[pos]
        row[pos] = new
        c = cost_of(sets)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
            if c < best_c:
                best_c = c
                best_s = _copy_sets(sets)
        else:
            row[pos] = old
    if best_c == 0:
        return cnt, best_s
    return None


def _orbit_phase(d, D, best_n, rng, deadline):
    """Try multi-orbit lifts with more than best_n vertices, smallest first. Returns (n, edges) or None."""
    moore = lib.moore_bound(d, D)
    cands = []
    for k in (2, 3):
        for N in range(best_n // (2 * k) + 1, moore // (2 * k) + 1):
            if N >= 2:
                cands.append((2 * k * N, k, N))
    cands.sort()

    best = None
    for n, k, N in cands:
        if n <= best_n:
            continue
        now = time.monotonic()
        if now >= deadline:
            break
        cand_end = now + max(3.0, (deadline - now) / 3.0)
        groups = _group_list(N, rng)
        found = None
        chosen_mul = None
        while time.monotonic() < cand_end and found is None:
            _, mul, _ = rng.choice(groups)
            res = _orbit_search(k, N, mul, d, rng,
                                min(cand_end, time.monotonic() + 4.0))
            if res is not None:
                found = res
                chosen_mul = mul
        if found is not None:
            cnt, sets = found
            darts = [(i, k + j, g) for i in range(k) for j in range(k)
                     for g in sets[i][j]]
            nn, e = lib.group_lift(2 * k, darts, N, chosen_mul)
            if nn > best_n and lib.is_valid(nn, e, d, D):
                best = (nn, e)
                best_n = nn
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e

    lo = base_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo <= hi:
        phase1_end = start + 0.3 * (deadline - start)
        r = _cayley_phase(d, lo, hi, rng, phase1_end)
        if r is not None and r[0] > best_n and lib.is_valid(r[0], r[1], d, D):
            best_n, best_e = r

    r = _orbit_phase(d, D, best_n, rng, deadline)
    if r is not None and r[0] > best_n:
        best_n, best_e = r

    return best_n, best_e
