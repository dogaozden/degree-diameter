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
# New construction: two-orbit voltage lift.
# Base graph has 4 vertices: A0, A1 (side A) and B0, B1 (side B). Darts are
# A_a -- B_b with a Z-group voltage g. Block counts are
#     [[p, d-p], [d-p, p]],  1 <= p <= d-1,
# so every base vertex has exactly d darts and the lift is d-regular and
# bipartite on 4N vertices. Voltages are annealed to minimise the number of
# vertex pairs at distance > 3 (the 'bad pairs' count).
# ----------------------------------------------------------------------------

def _mul_table(N, mul):
    return [[mul(x, g) for g in range(N)] for x in range(N)]


def _orbit_cost(N, mt, darts):
    """Number of unordered vertex pairs at distance > 3 in the lift of the 4-vertex base."""
    n = 4 * N
    adj = [[] for _ in range(n)]
    for a, b, g in darts:
        A = a * N
        B = b * N
        for x in range(N):
            u = A + x
            v = B + mt[x][g]
            adj[u].append(v)
            adj[v].append(u)
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _orbit_search(N, mt, d, rng, deadline, steps):
    """Simulated annealing over voltages of a two-orbit lift; returns darts with cost 0 or None."""
    p = rng.randint(1, d - 1)
    kinds = [(0, 2), (0, 3), (1, 2), (1, 3)]
    counts = [p, d - p, d - p, p]
    base = []
    for (a, b), c in zip(kinds, counts):
        base += [(a, b)] * c
    darts = [(a, b, rng.randrange(N)) for a, b in base]
    cost = _orbit_cost(N, mt, darts)
    T0 = 2.0
    for it in range(steps):
        if cost == 0:
            return darts
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(len(darts))
        a, b, g = darts[i]
        ng = rng.randrange(N)
        if ng == g:
            continue
        darts[i] = (a, b, ng)
        c2 = _orbit_cost(N, mt, darts)
        T = T0 * (1.0 - it / steps) + 0.05
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            darts[i] = (a, b, g)
    return darts if cost == 0 else None


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

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Stage 1: difference-cover group lifts (order 2N), first half of the budget.
    deadline_dc = start + 0.5 * total
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    for N in range(lo, hi + 1):
        if time.monotonic() >= deadline_dc:
            break
        if 2 * N <= best_n:
            continue
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        now = time.monotonic()
        deadline_N = now + 0.5 * max(0.0, deadline_dc - now)
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
        try:
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            consider(n, edges)
        except Exception:
            pass

    # Stage 2: two-orbit voltage lifts (order 4N) annealed for diameter 3.
    N = max(best_n // 4 + 1, d)
    hi4 = lib.moore_bound(d, 3) // 4
    while N <= hi4 and time.monotonic() < deadline:
        groups = _group_list(N, rng)
        mts = [_mul_table(N, g[1]) for g in groups]
        found = None
        now = time.monotonic()
        slice_end = min(deadline, now + max(3.0, 0.5 * (deadline - now)))
        while found is None and time.monotonic() < slice_end:
            for gi in range(len(groups)):
                if time.monotonic() >= slice_end:
                    break
                darts = _orbit_search(N, mts[gi], d, rng, slice_end, 2000)
                if darts is not None:
                    found = (gi, darts)
                    break
        if found is None:
            break
        gi, darts = found
        try:
            n, edges = lib.group_lift(4, darts, N, groups[gi][1])
            consider(n, edges)
        except Exception:
            pass
        N = max(N + 1, best_n // 4 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
