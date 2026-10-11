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


# ---------------------------------------------------------------- phase A
# Difference-cover lifts (order 2N, base = two vertices), as in the parent.

def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _upd(cnt, R, S, skip, v, sign):
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


def _anneal_diff(N, R, d, rng, steps, e):
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


def _diff_cover(d, best_n, rng, deadline, consider):
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    for N in range(lo, hi + 1):
        if time.monotonic() >= deadline:
            break
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
                S = _anneal_diff(N, R, d, rng, 6000, R[0][0])
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


# ---------------------------------------------------------------- phase B
# Bold change: base graph with k vertices per side (k = 2 or 3), darts with
# voltages in a group of order N, so the lift has 2kN vertices. The
# count matrix is a sum of d permutation matrices (row and column sums d).
# Annealing minimises the number of (root, vertex) pairs at distance > 3.
# Left multiplication is an automorphism, so BFS from one identity per
# fiber decides the diameter exactly.

def _tables(N, mul, inv):
    MT = [[mul(x, g) for x in range(N)] for g in range(N)]   # MT[g][x] = x*g
    RT = [[mul(y, inv(g)) for y in range(N)] for g in range(N)]  # RT[g][y] = y*g^-1
    return MT, RT


def _connected(k, C):
    adj = [[] for _ in range(2 * k)]
    for i in range(k):
        for j in range(k):
            if C[i][j]:
                adj[i].append(k + j)
                adj[k + j].append(i)
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == 2 * k


def _cost(k, N, darts, MT, RT):
    dfrom = [[] for _ in range(k)]
    dto = [[] for _ in range(k)]
    for i, j, g in darts:
        dfrom[i].append((k + j, MT[g]))
        dto[j].append((i, RT[g]))
    V = 2 * k * N
    bad = 0
    for rf in range(2 * k):
        dist = [-1] * V
        s = rf * N
        dist[s] = 0
        frontier = [s]
        seen = 1
        for depth in range(1, 4):
            nxt = []
            for v in frontier:
                f, x = divmod(v, N)
                if f < k:
                    for bf, tab in dfrom[f]:
                        w = bf * N + tab[x]
                        if dist[w] < 0:
                            dist[w] = depth
                            nxt.append(w)
                else:
                    for af, tab in dto[f - k]:
                        w = af * N + tab[x]
                        if dist[w] < 0:
                            dist[w] = depth
                            nxt.append(w)
            seen += len(nxt)
            frontier = nxt
            if not frontier:
                break
        bad += V - seen
    return bad


def _anneal_block(k, N, d, MT, RT, rng, end):
    while True:
        C = [[0] * k for _ in range(k)]
        for _ in range(d):
            p = list(range(k))
            rng.shuffle(p)
            for i in range(k):
                C[i][p[i]] += 1
        if _connected(k, C):
            break
    darts = []
    for i in range(k):
        for j in range(k):
            if C[i][j]:
                for g in rng.sample(range(N), C[i][j]):
                    darts.append([i, j, g])
    cur = _cost(k, N, darts, MT, RT)
    best = cur
    bestd = [list(t) for t in darts]
    start = time.monotonic()
    span = max(1e-3, end - start)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            break
        T = max(0.2, 2.5 * (1.0 - (now - start) / span))
        t = rng.randrange(len(darts))
        i, j, g = darts[t]
        used = {gg for ii, jj, gg in darts if ii == i and jj == j}
        ng = rng.randrange(N)
        if ng in used:
            continue
        darts[t][2] = ng
        new = _cost(k, N, darts, MT, RT)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if cur < best:
                best = cur
                bestd = [list(x) for x in darts]
        else:
            darts[t][2] = g
    return bestd if best == 0 else None


def _search_N(k, N, d, rng, att_end, cache):
    if N not in cache:
        groups = _group_list(N, rng)
        rng.shuffle(groups)
        cache[N] = {"groups": groups[:6], "tables": {}}
    ent = cache[N]
    groups = ent["groups"]
    r = 0
    while time.monotonic() < att_end:
        gi = r % len(groups)
        r += 1
        if gi not in ent["tables"]:
            ent["tables"][gi] = _tables(N, groups[gi][1], groups[gi][2])
        MT, RT = ent["tables"][gi]
        now = time.monotonic()
        sub_end = min(att_end, now + max(1.5, (att_end - now) / 2.0))
        darts = _anneal_block(k, N, d, MT, RT, rng, sub_end)
        if darts is not None:
            return darts, groups[gi][1]
    return None


def _block_search(d, best_n, rng, deadline, consider):
    moore = 2 * (d * d - d + 1)
    cache = {}
    T = best_n + 1
    while T <= moore:
        if time.monotonic() >= deadline:
            break
        cands = [k for k in (2, 3) if T % (2 * k) == 0 and T // (2 * k) >= d]
        if not cands:
            T += 1
            continue
        found = False
        for k in cands:
            N = T // (2 * k)
            now = time.monotonic()
            rem = deadline - now
            if rem <= 0:
                break
            att_end = now + min(rem, max(2.0, 0.35 * rem))
            res = _search_N(k, N, d, rng, att_end, cache)
            if res is not None:
                darts, mul = res
                try:
                    n, edges = lib.group_lift(2 * k, [(i, k + j, g) for i, j, g in darts], N, mul)
                    consider(n, edges)
                    found = True
                except Exception:
                    pass
                break
        if not found:
            break
        T += 1


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

    # Phase A: short difference-cover search (safe, parent method).
    try:
        _diff_cover(d, best_n, rng, start + 0.2 * total, consider)
    except Exception:
        pass

    # Phase B: bold search over k-vertex-per-side voltage lifts.
    try:
        _block_search(d, best_n, rng, deadline, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
