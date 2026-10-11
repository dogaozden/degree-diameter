import math
import random
import time

import lib

STEPS = 15000     # annealing steps per restart
T_START = 1.2     # annealing temperature schedule
T_END = 0.05


def _fallback(d, D):
    """Verified baseline graphs for every (d, D); the best applicable construction is used."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ difference-cover lifts
#
# Two base vertices a, b with darts (a, b, s), s in S, give the bipartite graph on
# G x {0,1} with a_x ~ b_{x s}. Every same-side pair is at distance <= 2 exactly when
# S S^{-1} = G, and then the diameter is <= 3. Order 2|G| with |G| <= d(d-1)+1.

def _groups(N, rng, cap=12):
    """Cyclic group of order N, plus semidirect products Z_m x| Z_k (r = 1 gives direct products)."""
    _, mul, inv = lib.cyclic_group(N)
    groups = [(mul, inv)]
    others = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in [1] + rs[:3]:
            try:
                _, mu, iv = lib.semidirect_group(m, k, r)
                others.append((mu, iv))
            except ValueError:
                pass
    rng.shuffle(others)
    groups += others[:cap - 1]
    return groups


def _table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _apply(cnt, R, others, v, sign):
    """Add (sign > 0) or remove (sign < 0) all ordered differences involving v and the set 'others'.

    The diagonal pair (v, v) contributes the identity. Returns the change in the number of
    uncovered group elements (zero entries of cnt).
    """
    rv = R[v]
    diffs = [rv[v]]
    for b in others:
        diffs.append(rv[b])
        diffs.append(R[b][v])
    ch = 0
    if sign > 0:
        for g in diffs:
            if cnt[g] == 0:
                ch -= 1
            cnt[g] += 1
    else:
        for g in diffs:
            cnt[g] -= 1
            if cnt[g] == 0:
                ch += 1
    return ch


def _try(N, R, d, rng, steps, deadline):
    """One annealing run for d elements S with S S^{-1} = G. Returns S or None."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    for a in S:
        ra = R[a]
        for b in S:
            cnt[ra[b]] += 1
    cost = cnt.count(0)
    if cost == 0:
        return S
    for it in range(steps):
        if (it & 2047) == 0 and time.monotonic() > deadline:
            return None
        T = T_START + (T_END - T_START) * it / steps
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        others = S[:i] + S[i + 1:]
        delta = _apply(cnt, R, others, old, -1)
        delta += _apply(cnt, R, others, x, 1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            cost += delta
            if cost == 0:
                return S
        else:
            _apply(cnt, R, others, x, -1)
            _apply(cnt, R, others, old, 1)
    return None


def _search(d, D, rng, deadline, best):
    """Ascending search over group orders N; returns the best (n, edges) found."""
    best_n = best[0]
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return best
    lo = best_n // 2 + 1
    hi = d * (d - 1) + 1
    fails = 0
    for N in range(max(lo, d), hi + 1):
        now = time.monotonic()
        if now >= deadline:
            break
        if 2 * N <= best_n:
            continue
        groups = _groups(N, rng)
        tables = [None] * len(groups)
        budget_end = min(deadline, now + max(2.0, 0.3 * (deadline - now)))
        found = None
        gi = 0
        while found is None and time.monotonic() < budget_end:
            idx = gi % len(groups)
            gi += 1
            if tables[idx] is None:
                mul, inv = groups[idx]
                tables[idx] = _table(N, mul, inv)
            S = _try(N, tables[idx], d, rng, STEPS, budget_end)
            if S is not None:
                found = (idx, S)
        if found is None:
            fails += 1
            if fails >= 4:
                break
            continue
        fails = 0
        idx, S = found
        mul = groups[idx][0]
        n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(2.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []
    best = (base_n, base_e)

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return best

    try:
        best = _search(d, D, rng, deadline, best)
    except Exception:
        pass
    return best
