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
    """Add or remove ordered differences of v against S[j], j != skip. Returns change in uncovered count."""
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


def _diff_cover_stage(d, lo, hi, deadline, rng, consider):
    """Difference-cover Haar lifts (order 2N with S S^{-1} = G, |S| = d), searched ascending in N."""
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


# ------------------------------------------------------------------
# New: multi-base voltage lifts searched by annealing.
#
# Base graph: k A-vertices and k B-vertices, every base vertex has d darts
# (a d-regular bipartite multigraph with k darts-per-side-vertex pattern, k*d darts total).
# Each dart (i, j, g) joins A_i fibre to B_j fibre with voltage g in a group G of order N.
# The lift has 2kN vertices. Group translations are automorphisms, so the diameter is
# the maximum eccentricity over the 2k base vertices (fibre representatives x = e).
# Annealing minimises the number of vertices not reached within distance 3 from those
# representatives. Cost zero means the lift has diameter <= 3.
# ------------------------------------------------------------------

def _mul_table(N, mul):
    return [[mul(x, g) for g in range(N)] for x in range(N)]


def _lift_cost(k, N, mulT, darts):
    """Number of (source, vertex) pairs not within distance 3, over the 2k base representatives."""
    kN = k * N
    n = 2 * kN
    adj = [[] for _ in range(n)]
    for i, j, g in darts:
        base_a = i * N
        base_b = kN + j * N
        for x in range(N):
            a = base_a + x
            b = base_b + mulT[x][g]
            adj[a].append(b)
            adj[b].append(a)
    cost = 0
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    for s in sources:
        seen = {s}
        frontier = [s]
        for _ in range(3):
            nxt = []
            for v in frontier:
                for u in adj[v]:
                    if u not in seen:
                        seen.add(u)
                        nxt.append(u)
            frontier = nxt
        cost += n - len(seen)
    return cost


def _base_edges(k, N, mulT, darts):
    """Expand base darts into the lifted edge list; returns (n, edges)."""
    kN = k * N
    edges = set()
    for i, j, g in darts:
        for x in range(N):
            a = i * N + x
            b = kN + j * N + mulT[x][g]
            edges.add((a, b))
    return 2 * kN, sorted(edges)


def _anneal_base(k, d, N, mulT, rng, budget):
    """Anneal dart endpoints and voltages until the lift has diameter <= 3; None on timeout."""
    t_start = time.monotonic()
    t_end = t_start + budget
    A_st = [i for i in range(k) for _ in range(d)]
    B_st = list(A_st)
    rng.shuffle(B_st)
    darts = [[A_st[t], B_st[t], rng.randrange(N)] for t in range(k * d)]
    m = len(darts)
    cost = _lift_cost(k, N, mulT, darts)
    while cost > 0:
        now = time.monotonic()
        if now >= t_end:
            return None
        frac = (now - t_start) / max(budget, 1e-6)
        T = 1.5 * (1.0 - frac) + 0.05
        r = rng.random()
        t1 = rng.randrange(m)
        if r < 0.6:
            old = darts[t1][2]
            darts[t1][2] = rng.randrange(N)
            new = _lift_cost(k, N, mulT, darts)
            if new <= cost or rng.random() < math.exp((cost - new) / T):
                cost = new
            else:
                darts[t1][2] = old
        else:
            t2 = rng.randrange(m)
            if t2 == t1:
                continue
            pos = 1 if r < 0.8 else 0
            darts[t1][pos], darts[t2][pos] = darts[t2][pos], darts[t1][pos]
            new = _lift_cost(k, N, mulT, darts)
            if new <= cost or rng.random() < math.exp((cost - new) / T):
                cost = new
            else:
                darts[t1][pos], darts[t2][pos] = darts[t2][pos], darts[t1][pos]
    return darts


def _search_lift(k, d, N, rng, budget):
    """Random restarts over groups of order N; returns (n, edges) on success, else None."""
    groups = _group_list(N, rng)
    tables = [None] * len(groups)
    end = time.monotonic() + budget
    restart = max(1.5, 0.3 * budget)
    while True:
        now = time.monotonic()
        if now >= end:
            return None
        idx = rng.randrange(len(groups))
        if tables[idx] is None:
            tables[idx] = _mul_table(N, groups[idx][1])
        mulT = tables[idx]
        darts = _anneal_base(k, d, N, mulT, rng, min(end - now, restart))
        if darts is not None:
            return _base_edges(k, N, mulT, darts)


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

    # Stage 1: difference-cover Haar lifts (k = 1), a short slice of the budget.
    try:
        now = time.monotonic()
        diff_deadline = now + 0.25 * max(0.0, deadline - now)
        _diff_cover_stage(d, best_n // 2 + 1, d * (d - 1) + 1, diff_deadline, rng, consider)
    except Exception:
        pass

    # Stage 2: multi-base voltage lifts with k = 2, 3, 4 darts-per-side patterns.
    # Ladder over N: each success raises the target order 2kN.
    moore = lib.moore_bound(d, D)
    ks = [2, 3, 4]
    try:
        for pos, k in enumerate(ks):
            now = time.monotonic()
            if now >= deadline:
                break
            k_deadline = now + (deadline - now) / (len(ks) - pos)
            N = best_n // (2 * k) + 1
            Nmax = moore // (2 * k)
            while N <= Nmax:
                now = time.monotonic()
                left = k_deadline - now
                if left < 1.0:
                    break
                budget = min(left, max(4.0, 0.5 * left))
                res = _search_lift(k, d, N, rng, budget)
                if res is None:
                    break
                consider(*res)
                N = max(N + 1, best_n // (2 * k) + 1)
    except Exception:
        pass

    return best
