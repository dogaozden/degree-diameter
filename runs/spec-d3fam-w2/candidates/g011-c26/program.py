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


def _diff_cover_stage(d, D, rng, best_n, deadline):
    """Parent's difference-cover lift search (order 2N). Returns best valid (n, edges) found or None."""
    result = None
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    for N in range(lo, hi + 1):
        if time.monotonic() >= deadline:
            break
        if 2 * N <= best_n:
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
            if n > best_n and lib.is_valid(n, edges, d, D):
                result = (n, edges)
                best_n = n
        except Exception:
            pass
    return result


def _voltage_anneal(d, D, k, N, rng, deadline):
    """Different construction: a bipartite base with k+k vertices and d darts per A-vertex,
    lifted over a group of order N. Voltages are annealed to minimise the number of vertex
    pairs at distance more than D. Returns (n, edges) with zero bad pairs, or None on timeout.
    """
    groups = _group_list(N, rng)
    _, mul, _ = groups[rng.randrange(len(groups))]
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + perms[t][i], rng.randrange(N)] for t in range(d) for i in range(k)]

    def score():
        n, edges = lib.group_lift(2 * k, darts, N, mul)
        return lib.bad_pairs(n, edges, D), n, edges

    cur, n, edges = score()
    it = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        it += 1
        T = max(0.15, 1.0 * (0.999 ** it))
        j = rng.randrange(len(darts))
        old = darts[j][2]
        new = rng.randrange(N)
        if new == old:
            continue
        darts[j][2] = new
        c2, n2, e2 = score()
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur, n, edges = c2, n2, e2
        else:
            darts[j][2] = old
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
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

    total = max(0.0, deadline - start)

    # Stage 1 (about 40% of the budget): parent's difference-cover lifts.
    try:
        res = _diff_cover_stage(d, D, rng, best_n, start + 0.4 * total)
        if res is not None:
            consider(*res)
    except Exception:
        pass

    # Stage 2 (remaining budget): voltage lifts over k+k base vertices with
    # annealed voltages, aiming for orders 2kN above the current best.
    for k in (3, 2, 4):
        now = time.monotonic()
        if now >= deadline:
            break
        remaining_ks = 3 if k == 3 else (2 if k == 2 else 1)
        k_deadline = now + (deadline - now) / remaining_ks
        N_max = lib.moore_bound(d, D) // (2 * k)
        N = max(best_n // (2 * k) + 1, d)
        while N <= N_max and time.monotonic() < k_deadline:
            try:
                res = _voltage_anneal(d, D, k, N, rng, k_deadline)
            except Exception:
                res = None
            if res is None:
                break
            consider(*res)
            N = max(best_n // (2 * k) + 1, N + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
