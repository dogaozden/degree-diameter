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


def _tables(N, mul, inv):
    """Return (M, iv, Dt): M[x][y] = x*y, iv[y] = y^{-1}, Dt[x][y] = x*y^{-1}. Identity is element 0."""
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    iv = [inv(y) for y in range(N)]
    Dt = [[M[x][iv[y]] for y in range(N)] for x in range(N)]
    return M, iv, Dt


def _search(N, M, iv, Dt, d, rng, node_limit, deadline):
    """Randomized depth-first search for S (|S| <= d, 0 in S) with S S^{-1} = G.

    Branches only on elements that cover a chosen uncovered difference g against
    elements already in S, so it is a heuristic (not complete). Returns S or None.
    """
    cnt = [0] * N
    cnt[0] = 1
    state = {"unc": N - 1}
    S = [0]
    nodes = [0]
    order = list(range(1, N))
    rng.shuffle(order)

    def add(x):
        for y in S:
            for g in (Dt[x][y], Dt[y][x]):
                if cnt[g] == 0:
                    state["unc"] -= 1
                cnt[g] += 1
        S.append(x)

    def remove(x):
        S.pop()
        for y in S:
            for g in (Dt[x][y], Dt[y][x]):
                cnt[g] -= 1
                if cnt[g] == 0:
                    state["unc"] += 1

    def dfs():
        if state["unc"] == 0:
            return True
        s = len(S)
        if s >= d:
            return False
        nodes[0] += 1
        if nodes[0] > node_limit:
            return False
        if (nodes[0] & 127) == 0 and time.monotonic() > deadline:
            return False
        # Each future element adds at most 2*(current size) new ordered differences.
        r = d - s
        bound = sum(2 * (s + j) for j in range(r))
        if state["unc"] > bound:
            return False
        g = next(x for x in order if cnt[x] == 0)
        cands = set()
        ig = iv[g]
        for y in S:
            cands.add(M[g][y])
            cands.add(M[ig][y])
        cands.difference_update(S)
        cl = list(cands)
        rng.shuffle(cl)
        for x in cl:
            add(x)
            if dfs():
                return True
            remove(x)
        return False

    if dfs():
        return list(S)
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

    # Haar lifts over a group G of order N with S S^{-1} = G, |S| = d, give order 2N.
    # Search descending in N with growing node budgets (restarts across groups).
    hi = d * (d - 1) + 1
    cache = {}
    limit = 3000
    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        if lo > hi:
            break
        progressed = False
        for N in range(hi, lo - 1, -1):
            if time.monotonic() >= deadline:
                break
            if N not in cache:
                try:
                    groups = _group_list(N, rng)
                except Exception:
                    groups = []
                cache[N] = (groups, [None] * len(groups))
            groups, tabs = cache[N]
            if not groups:
                continue
            found = None
            attempts = 2 * len(groups)
            for _ in range(attempts):
                if time.monotonic() >= deadline:
                    break
                idx = rng.randrange(len(groups))
                if tabs[idx] is None:
                    _, mul, inv = groups[idx]
                    tabs[idx] = _tables(N, mul, inv)
                M, iv, Dt = tabs[idx]
                S = _search(N, M, iv, Dt, d, rng, limit, deadline)
                if S is not None:
                    found = (idx, S)
                    break
            if found is not None:
                idx, S = found
                mul = groups[idx][1]
                try:
                    n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
                    consider(n, edges)
                    progressed = True
                except Exception:
                    pass
                break
        if not progressed:
            limit *= 2

    return best
