import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline graphs. Araujo-Pardo & Lopez record for D = 3, Moore-extremal when d-1 is a prime power."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))              # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)    # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)        # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s), s in S, give the bipartite graph
# on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 when S S^{-1} = G.
# So we need a difference cover S of size d in a group G of order N, giving
# order 2N with N <= d(d-1)+1.
#
# Left-translation invariance: if S S^{-1} = G then so does gS, so WLOG the
# identity (index 0) is in S. This shrinks the search space.

def _group_list(N, rng):
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k of order N."""
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
        for r in rs[:3]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _upd(cnt, R, S, skip, v, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences of v against S[j], j != skip.

    Returns the change in the number of uncovered group elements.
    """
    ch = 0
    Rv = R[v]
    for j, b in enumerate(S):
        if j == skip:
            continue
        for g in (Rv[b], R[b][v]):
            if sign > 0:
                if cnt[g] == 0:
                    ch -= 1
                cnt[g] += 1
            else:
                cnt[g] -= 1
                if cnt[g] == 0:
                    ch += 1
    return ch


def _search(N, mul, inv, d, rng):
    """Generator: annealing for S (containing identity 0) with S S^{-1} = G.

    Yields None periodically so the driver can round-robin across entries,
    and yields the cover S once found.
    """
    R = _ratio_table(N, mul, inv)
    steps = 40000
    while True:
        S = [0] + rng.sample(range(1, N), d - 1)
        cnt = [0] * N
        cnt[0] = 1                      # identity covered by a = b
        for a in S:
            for b in S:
                if a != b:
                    cnt[R[a][b]] += 1
        unc = cnt.count(0)
        for it in range(steps):
            if unc == 0:
                break
            if it % 500 == 0:
                yield None
            T = 1.0 - 0.95 * it / steps
            i = rng.randrange(1, d)     # index 0 stays the identity
            x = rng.randrange(N)
            if x in S:
                continue
            old = S[i]
            delta = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, 1)
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S[i] = x
                unc += delta
            else:
                _upd(cnt, R, S, i, x, -1)
                _upd(cnt, R, S, i, old, 1)
        if unc == 0:
            yield list(S)
            return


# ---------------------------------------------------------------- driver

WINDOW = 3   # number of group orders N searched at once (lowest first)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    base = _fallback(d, D)
    if not lib.is_valid(base[0], base[1], d, D):
        return 1, []

    # Moore-extremal and out-of-regime cases keep the baseline.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base

    best_box = [base[0]]
    best_pair = [base]
    lo = max(best_box[0] // 2 + 1, d)   # need 2N > best order
    hi = d * (d - 1) + 1
    if lo > hi:
        return base

    entries = []        # each: [N, mul, generator]
    next_N = [lo]

    def refill():
        active = {e[0] for e in entries}
        while len(active) < WINDOW and next_N[0] <= hi:
            N = next_N[0]
            next_N[0] += 1
            if 2 * N <= best_box[0]:
                continue
            active.add(N)
            for _o, mul, inv in _group_list(N, rng):
                entries.append([N, mul, _search(N, mul, inv, d, rng)])

    try:
        refill()
        while time.monotonic() < deadline:
            refill()
            if not entries:
                break
            for ent in list(entries):
                if time.monotonic() >= deadline:
                    break
                N, mul, gen = ent
                if 2 * N <= best_box[0]:
                    entries.remove(ent)
                    continue
                try:
                    res = next(gen)
                except StopIteration:
                    entries.remove(ent)
                    continue
                if res is None:
                    continue
                entries.remove(ent)
                try:
                    n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
                except Exception:
                    continue
                if n > best_box[0] and lib.is_valid(n, edges, d, D):
                    best_pair[0] = (n, edges)
                    best_box[0] = n
                    entries[:] = [e for e in entries if 2 * e[0] > n]
                    next_N[0] = max(next_N[0], n // 2 + 1)
                    break
    except Exception:
        pass

    best = best_pair[0]
    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
