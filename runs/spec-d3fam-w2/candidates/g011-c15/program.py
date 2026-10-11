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


def _diffcover(d, rng, st, deadline, consider):
    """Phase 1: difference-cover group lifts with 2 base vertices (the parent's search)."""
    hi = d * (d - 1) + 1
    lo = max(st["n"] // 2 + 1, d)
    for N in range(lo, hi + 1):
        if time.monotonic() >= deadline:
            break
        if 2 * N <= st["n"]:
            continue
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        now = time.monotonic()
        deadline_N = now + 0.5 * max(0.0, deadline - now)
        while found is None and time.monotonic() < deadline_N:
            for idx in range(len(groups)):
                if time.monotonic() >= deadline_N:
                    break
                if tables[idx] is None:
                    tables[idx] = _ratio_table(N, groups[idx][1], groups[idx][2])
                R = tables[idx]
                S = _anneal(N, R, d, rng, 6000, R[0][0])
                if S is not None:
                    found = (idx, S)
                    break
        if found is None:
            break
        idx, S = found
        try:
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, groups[idx][1])
            consider(n, edges)
        except Exception:
            pass


def _random_base(k, d, rng):
    """k x k dart-count matrix with all row and column sums equal to d (sum of d permutations)."""
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            M[i][perm[i]] += 1
    return M


def _sa_lift(k, M, m, D, rng, t_end):
    """Phase 2 search: anneal Z_m voltages on a bipartite base with k+k vertices.

    Base vertices 0..k-1 form side A, k..2k-1 form side B; the lift has 2k*m vertices.
    Cost is the number of vertex pairs at distance > D. Returns (n, edges) or None.
    """
    base_n = 2 * k
    darts = []
    for i in range(k):
        for j in range(k):
            for _ in range(M[i][j]):
                darts.append([i, k + j, rng.randrange(m)])

    def evaluate(ds):
        n, edges = lib.voltage_lift(base_n, [tuple(x) for x in ds], m)
        return lib.bad_pairs(n, edges, D), n, edges

    cur, n, edges = evaluate(darts)
    if cur == 0:
        return n, edges
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    while time.monotonic() < t_end and darts:
        frac = (time.monotonic() - t0) / span
        T = 1.5 * (1.0 - frac) + 0.05
        idx = rng.randrange(len(darts))
        old = darts[idx][2]
        darts[idx][2] = rng.randrange(m)
        c, n2, e2 = evaluate(darts)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
            if c == 0:
                return n2, e2
        else:
            darts[idx][2] = old
    return None


def _voltage_search(d, D, rng, st, deadline, consider):
    """Phase 2: repeatedly search larger voltage lifts on random small base graphs."""
    fails = 0
    while time.monotonic() < deadline - 0.5:
        k = rng.choice((2, 2, 3))
        m = st["n"] // (2 * k) + 1  # need 2k*m > current best order
        M = _random_base(k, d, rng)
        now = time.monotonic()
        slice_end = min(deadline, now + 6.0 + 3.0 * min(fails, 6))
        try:
            res = _sa_lift(k, M, m, D, rng, slice_end)
        except Exception:
            res = None
        if res is not None:
            consider(*res)
            fails = 0
        else:
            fails += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    st = {"n": best[0], "e": best[1]}

    def consider(n, e):
        if n > st["n"] and lib.is_valid(n, e, d, D):
            st["n"], st["e"] = n, e

    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return st["n"], st["e"]

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    try:
        now = time.monotonic()
        p1 = now + 0.3 * max(0.0, deadline - now)
        _diffcover(d, rng, st, p1, consider)
    except Exception:
        pass

    try:
        _voltage_search(d, D, rng, st, deadline, consider)
    except Exception:
        pass

    result = (st["n"], st["e"])
    if not lib.is_valid(result[0], result[1], d, D):
        return _fallback(d, D)
    return result
