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


def _search_lift4(d, N, rng, deadline):
    """Search a 2x2-base voltage lift (order 4N, degree d, diameter 3).

    Base: A0, A1 on one side, B0, B1 on the other, with dart multiplicities
    [[k, d-k], [d-k, k]]. Voltages are random, then repaired by local search
    minimising the number of pairs at distance > 3. Returns (n, edges) or None.
    """
    n = 4 * N
    while time.monotonic() < deadline:
        groups = _group_list(N, rng)
        mul = groups[rng.randrange(len(groups))][1]
        k = rng.randrange(1, d)
        mult = [((0, 2), k), ((0, 3), d - k), ((1, 2), d - k), ((1, 3), k)]
        darts = []   # entries are [pair, voltage]
        used = {}
        for pair, m in mult:
            vs = rng.sample(range(N), m)
            used[pair] = set(vs)
            for g in vs:
                darts.append([pair, g])

        def lift():
            return lib.group_lift(4, [(p[0], p[1], g) for p, g in darts], N, mul)

        _, edges = lift()
        cur = lib.bad_pairs(n, edges, 3)
        steps = 0
        while cur > 0 and steps < 4000 and time.monotonic() < deadline:
            steps += 1
            t = rng.randrange(len(darts))
            pair, old = darts[t]
            g = rng.randrange(N)
            if g in used[pair]:
                continue
            used[pair].discard(old)
            used[pair].add(g)
            darts[t][1] = g
            _, cand = lift()
            nb = lib.bad_pairs(n, cand, 3)
            if nb <= cur or rng.random() < 0.02:
                cur = nb
                edges = cand
            else:
                used[pair].discard(g)
                used[pair].add(old)
                darts[t][1] = old
        if cur == 0:
            return n, edges
    return None


def _lift4_search(d, best_n, rng, deadline):
    """Try 2x2-base lifts of order 4N with 4N > best_n, largest N first."""
    hi = lib.moore_bound(d, 3) // 4
    lo = best_n // 4 + 1
    Ns = [N for N in range(hi, lo - 1, -1) if N >= d]
    for idx, N in enumerate(Ns):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(Ns) - idx)
        res = _search_lift4(d, N, rng, slice_end)
        if res is not None:
            return res
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

    # New construction: 2x2-base voltage lifts repaired by local search.
    if d >= 5:
        try:
            res = _lift4_search(d, best_n, rng, start + 0.6 * total)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    # Difference-cover Haar lifts: order 2N needs S S^{-1} = G with |S| = d.
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= deadline:
            break
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        deadline_N = time.monotonic() + 0.5 * max(0.0, deadline - time.monotonic())
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

    return best
