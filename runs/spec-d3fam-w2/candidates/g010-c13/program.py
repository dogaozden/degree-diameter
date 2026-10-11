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
    """Add (sign=+1) or remove (sign=-1) ordered differences of v against S[j], j != skip."""
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


def _diff_search(d, D, best_n, rng, dl):
    """Parent's difference-cover group-lift search (order 2N); returns (n, edges) or None."""
    result = None
    bn = best_n
    hi = d * (d - 1) + 1
    lo = max(bn // 2 + 1, d)
    for N in range(lo, hi + 1):
        if time.monotonic() >= dl:
            break
        if 2 * N <= bn:
            continue
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        now = time.monotonic()
        deadline_N = now + 0.5 * max(0.0, dl - now)
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
            if n > bn and lib.is_valid(n, edges, d, D):
                result = (n, edges)
                bn = n
        except Exception:
            pass
    return result


# ---------------------------------------------------------------------------
# New construction: 4-vertex bipartite base (A0, A1 | B0, B1) lifted over a
# finite group of order N, so the lift has 4N vertices. Voltages are found by
# simulated annealing on the number of (base fiber, vertex) pairs that are not
# within distance 3 of the fiber's identity vertex. Left translations are
# automorphisms of a group lift, so zero uncovered pairs from the four base
# representatives certifies diameter <= 3 for the whole graph.
# ---------------------------------------------------------------------------

def _cost(N, table, darts):
    """Number of (representative, vertex) pairs not within distance 3 of the representative."""
    n = 4 * N
    adj = [[] for _ in range(n)]
    for u, v, g in darts:
        ub = u * N
        vb = v * N
        for x in range(N):
            a = ub + x
            b = vb + table[x][g]
            adj[a].append(b)
            adj[b].append(a)
    bad = 0
    for s in (0, N, 2 * N, 3 * N):  # identity vertex of each base fiber
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        reached = 1
        for _ in range(3):
            nxt = []
            for a in frontier:
                for b in adj[a]:
                    if not seen[b]:
                        seen[b] = 1
                        nxt.append(b)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        bad += n - reached
    return bad


def _hill(N, table, d, p, rng, steps, dl):
    """Anneal voltages for base counts [[p, d-p], [d-p, p]]; return darts with zero cost or None."""
    darts = []
    for u, v, c in ((0, 2, p), (0, 3, d - p), (1, 2, d - p), (1, 3, p)):
        for _ in range(c):
            darts.append([u, v, rng.randrange(N)])
    cost = _cost(N, table, darts)
    for it in range(steps):
        if cost == 0:
            return darts
        if it % 50 == 0 and time.monotonic() >= dl:
            return None
        i = rng.randrange(len(darts))
        old = darts[i][2]
        darts[i][2] = rng.randrange(N)
        c2 = _cost(N, table, darts)
        T = 3.0 * (1.0 - it / steps) + 0.05
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            darts[i][2] = old
    return darts if cost == 0 else None


def _lift_search(d, D, best_n, rng, dl):
    """Search 4-vertex base lifts with order 4N > best_n; return best valid (n, edges) or None."""
    best = None
    bn = best_n
    N = bn // 4 + 1
    while time.monotonic() < dl:
        groups = _group_list(N, rng)
        got = None
        while time.monotonic() < dl and got is None:
            order, mul, inv = groups[rng.randrange(len(groups))]
            table = [[mul(x, y) for y in range(N)] for x in range(N)]
            p = rng.randint(1, d - 1)
            darts = _hill(N, table, d, p, rng, 3000, dl)
            if darts is not None:
                got = (mul, darts)
        if got is None:
            break
        mul, darts = got
        try:
            n, edges = lib.group_lift(4, [(u, v, g) for u, v, g in darts], N, mul)
            if n > bn and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                bn = n
        except Exception:
            pass
        N += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    # Parent's difference-cover search gets a bounded share of the budget.
    try:
        r = _diff_search(d, D, best[0], rng, start + 0.4 * total)
        if r is not None:
            consider(*r)
    except Exception:
        pass

    # Bold change: 4-vertex base voltage lifts, searched over the remaining time.
    try:
        r = _lift_search(d, D, best[0], rng, deadline)
        if r is not None:
            consider(*r)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
