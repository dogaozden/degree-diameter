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


def _lift4_search(d, N, groups, rng, deadline):
    """Search voltages for a 4-vertex bipartite lift (A={0,1}, B={2,3}) of order 4N with diameter <= 3.

    Base darts: m(0,2)=a, m(0,3)=m(1,2)=d-a, m(1,3)=a, so every base vertex has degree d.
    Local search minimises the number of vertex pairs at distance > 3 (lib.bad_pairs).
    Returns (n, edges) on success, or None when the deadline passes.
    """
    while time.monotonic() < deadline:
        order, mul, _ = groups[rng.randrange(len(groups))]
        a = rng.randint(0, d)
        pairs = ([(0, 2)] * a + [(0, 3)] * (d - a)
                 + [(1, 2)] * (d - a) + [(1, 3)] * a)
        vs = [rng.randrange(order) for _ in pairs]

        def score(vals):
            darts = [(u, v, g) for (u, v), g in zip(pairs, vals)]
            n, e = lib.group_lift(4, darts, order, mul)
            return lib.bad_pairs(n, e, 3), n, e

        cur, n, e = score(vs)
        stall = 0
        while cur > 0 and stall < 400 and time.monotonic() < deadline:
            i = rng.randrange(len(vs))
            old = vs[i]
            vs[i] = rng.randrange(order)
            val, n2, e2 = score(vs)
            if val <= cur or rng.random() < math.exp(-(val - cur) / 0.6):
                stall = 0 if val < cur else stall + 1
                cur, n, e = val, n2, e2
            else:
                vs[i] = old
                stall += 1
        if cur == 0:
            return n, e
    return None


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

    # Stage 1: difference-cover Haar lifts (order 2N, S S^{-1} = G with |S| = d).
    try:
        haar_deadline = time.monotonic() + 0.3 * max(0.0, deadline - time.monotonic())
        hi = d * (d - 1) + 1
        lo = best_n // 2 + 1
        for N in range(max(lo, d), hi + 1):
            if time.monotonic() >= haar_deadline:
                break
            groups = _group_list(N, rng)
            tables = [None] * len(groups)
            found = None
            deadline_N = time.monotonic() + 0.5 * max(0.0, haar_deadline - time.monotonic())
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
    except Exception:
        pass

    # Stage 2: 4-vertex bipartite voltage lifts of order 4N, searched by local
    # minimisation of pairs at distance > 3. Each success must beat best_n.
    try:
        N = best_n // 4 + 1
        N_max = lib.moore_bound(d, D) // 4
        while N <= N_max and time.monotonic() < deadline:
            groups = _group_list(N, rng)
            remaining = max(0.0, deadline - time.monotonic())
            budget_end = time.monotonic() + max(2.0, 0.6 * remaining)
            res = _lift4_search(d, N, groups, rng, min(deadline, budget_end))
            if res is None:
                break
            consider(*res)
            N = max(N + 1, best_n // 4 + 1)
    except Exception:
        pass

    return best
