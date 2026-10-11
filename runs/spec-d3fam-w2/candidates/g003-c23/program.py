import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


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
    """Add (sign=+1) or remove (sign=-1) ordered differences of v against S[j], j != skip.

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


def _anneal(N, R, d, rng, steps, e):
    """Find d distinct elements S with S S^{-1} = G by annealing; None if not found."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[e] = 1
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    for it in range(steps):
        T = 1.0 - 0.95 * it / steps
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        delta = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, +1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _upd(cnt, R, S, i, x, -1)
            _upd(cnt, R, S, i, old, +1)
    return None


# ----------------------------------------------------------------------------
# New routine: 2+2 voltage lifts.
# The base graph has two vertices on each side (A = {0,1}, B = {2,3}) and the
# dart counts are k, d-k, d-k, k, so every base vertex has degree d. A lift over
# a group of order N has 4N vertices. Darts within one base pair get distinct
# voltages, so the lift is exactly d-regular and simple. Voltages are found by
# simulated annealing on the number of vertex pairs at distance greater than 3.
# ----------------------------------------------------------------------------

_PAIRS = [(0, 2), (0, 3), (1, 2), (1, 3)]


def _voltage_cost(N, mul, sets, D):
    """Return (bad pair count, n, edges) for the 2+2 lift with the given voltage sets."""
    darts = [(u, v, g) for (u, v), s in sets.items() for g in s]
    n, e = lib.group_lift(4, darts, N, mul)
    return lib.bad_pairs(n, e, D), n, e


def _base4_search(d, D, N, groups, rng, deadline):
    """Search 2+2 voltage lifts over a group of order N; return (n, edges) with diameter <= D, or None."""
    while time.monotonic() < deadline:
        order, mul, _ = rng.choice(groups)
        k = rng.randint(1, d - 1)
        counts = {(0, 2): k, (0, 3): d - k, (1, 2): d - k, (1, 3): k}
        if any(c > N for c in counts.values()):
            return None
        sets = {p: rng.sample(range(N), counts[p]) for p in _PAIRS}
        cost, n, e = _voltage_cost(N, mul, sets, D)
        if cost == 0:
            return n, e
        T = 1.0
        for _ in range(4000):
            if time.monotonic() >= deadline:
                return None
            p = rng.choice(_PAIRS)
            s = sets[p]
            i = rng.randrange(len(s))
            g = rng.randrange(N)
            if g in s:
                continue
            old = s[i]
            s[i] = g
            c2, n2, e2 = _voltage_cost(N, mul, sets, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost, n, e = c2, n2, e2
                if cost == 0:
                    return n, e
            else:
                s[i] = old
            T = max(0.05, T * 0.999)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1).
    if lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Phase 1: difference-cover Haar lifts (order 2N, S S^{-1} = G, |S| = d),
    # capped at 30% of the budget.
    phase1_deadline = start + 0.3 * total
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= phase1_deadline:
            break
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        deadline_N = time.monotonic() + 0.5 * max(0.0, phase1_deadline - time.monotonic())
        while found is None and time.monotonic() < deadline_N:
            for idx in range(len(groups)):
                if time.monotonic() >= deadline_N:
                    break
                if tables[idx] is None:
                    mul, inv = groups[idx][1], groups[idx][2]
                    tables[idx] = _ratio_table(N, mul, inv)
                R = tables[idx]
                S = _anneal(N, R, d, rng, 6000, R[0][0])
                if S is not None:
                    found = (idx, S)
                    break
        if found is None:
            break
        idx, S = found
        mul = groups[idx][1]
        n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
        consider(n, edges)

    # Phase 2: 2+2 voltage lifts (4N vertices). Only N with 4N > best_n can improve.
    lo2 = best_n // 4 + 1
    hi2 = lib.moore_bound(d, D) // 4
    N = lo2
    while N <= hi2 and time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        deadline_N = now + 0.4 * remaining
        groups = _group_list(N, rng)
        res = _base4_search(d, D, N, groups, rng, deadline_N)
        if res is not None:
            consider(*res)
            N = max(N + 1, best_n // 4 + 1)
        else:
            N += 1

    return best
