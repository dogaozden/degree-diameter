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


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 when
# S S^{-1} = G, i.e. a "difference cover" of size d in G, order 2|G|.
#
# Changed from the parent: the search now draws on a much wider family of
# groups (all semidirect Z_m x| Z_k with every valid r, plus non-cyclic
# abelian Z_a x Z_b), and the annealer is run over all of them round-robin.

def _abelian(a, b):
    """Z_a x Z_b with element (x, y) coded as x*b + y."""
    N = a * b

    def mul(u, v):
        return ((u // b + v // b) % a) * b + (u % b + v % b) % b

    def inv(u):
        return ((-(u // b)) % a) * b + (-(u % b)) % b

    return N, mul, inv


def _group_list(N, rng, per_order_cap):
    """Many candidate groups of order N: cyclic, abelian, and semidirect."""
    groups = [lib.cyclic_group(N)]
    # Non-cyclic abelian groups Z_a x Z_b with a | b, a >= 2.
    for a in range(2, N + 1):
        if N % a == 0 and (N // a) % a == 0 and a * a <= N:
            groups.append(_abelian(a, N // a))
    # Semidirect Z_m x| Z_k with every admissible r.
    extra = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:per_order_cap]:
            try:
                extra.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    rng.shuffle(extra)
    groups.extend(extra)
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
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
    """Generator: incremental annealing for d elements S with S S^{-1} = G.

    Yields None periodically so the driver can round-robin many groups, and
    yields the cover S once found. Restarts from a fresh random state on stall.
    """
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


# ---------------------------------------------------------------- driver

def _search(d, D, base_n, rng, deadline):
    """Return a verified (n, edges) beating base_n, or None."""
    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return None

    active = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng, 6):
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
            if n > base_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    try:
        base_n, base_e = _fallback(d, D)
    except Exception:
        return 1, []
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    try:
        best = _search(d, D, base_n, rng, deadline)
    except Exception:
        best = None

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
