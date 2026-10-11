import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline graphs for small parameters or non-searched regimes."""
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
# S S^{-1} = G. So we need a "difference cover" S of size d in a group G of
# order N, giving a graph of order 2N with N <= d(d-1)+1.

def _cyclic(N):
    return (lambda x, y: (x + y) % N), (lambda x: (-x) % N)


def _abelian(a, b):
    """Z_a x Z_b, element (i, j) coded as i*b + j. Returns (mul, inv)."""
    def mul(x, y):
        i1, j1 = divmod(x, b)
        i2, j2 = divmod(y, b)
        return ((i1 + i2) % a) * b + (j1 + j2) % b

    def inv(x):
        i, j = divmod(x, b)
        return ((-i) % a) * b + (-j) % b

    return mul, inv


def _group_list(N, rng):
    """Candidate groups of order N as (mul, inv): cyclic, non-cyclic abelian, metacyclic."""
    groups = [_cyclic(N)]
    for a in range(2, N):
        if N % a == 0:
            b = N // a
            if a <= b and math.gcd(a, b) > 1:
                groups.append(_abelian(a, b))
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r)[1:])
            except ValueError:
                pass
    return groups


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
    """Generator: incremental annealing for d elements S with S S^{-1} = G.

    Yields None periodically so the driver can round-robin many groups, and
    yields the cover S once found. Restarts from a fresh random state on stall.
    """
    iv = [inv(y) for y in range(N)]
    R = [[mul(x, iv[y]) for y in range(N)] for x in range(N)]
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
            T = max(0.12, 0.6 * (1.0 - step / steps))
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


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit - 2.0, time_limit - 6.0))
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []
    best = (base_n, base_e)

    # Only the diameter-3 regime is searched. The Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return best

    hi = d * (d - 1) + 1              # hard bound for difference covers
    lo = max(base_n // 2 + 1, d)      # need 2N > current best and N >= d
    if lo > hi:
        return best

    # Entries: [N, mul, generator-or-None]. Larger groups are attempted first.
    active = []
    for N in range(hi, lo - 1, -1):
        for mul, inv in _group_list(N, rng):
            active.append([N, mul, _anneal(N, mul, inv, d, rng)])

    best_N = lo - 1
    while time.monotonic() < deadline:
        active = [e for e in active if e[2] is not None and e[0] > best_N]
        if not active:
            break
        for e in list(active):
            if time.monotonic() >= deadline:
                break
            if e[2] is None or e[0] <= best_N:
                continue
            try:
                res = next(e[2])
            except StopIteration:
                e[2] = None
                continue
            if res is None:
                continue
            N, mul = e[0], e[1]
            e[2] = None  # this generator has produced its cover
            n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
            active = [x for x in active if x[2] is not None and x[0] > best_N]

    return best
