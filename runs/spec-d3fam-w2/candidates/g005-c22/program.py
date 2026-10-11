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


# ---------------------------------------------------------------------------
# New construction: 2x2 base group lift.
# Base bipartite multigraph with A = {a0, a1}, B = {b0, b1}. Darts (a, b, g) with
# voltages in a group G of order N. Vertex (a, x) joins (b, x*g) for each dart.
# Degree counts: c00 = t, c01 = c10 = d - t, c11 = t, so every base vertex has
# degree d. The lift has 4N vertices and is bipartite by construction.
# Diameter <= 3 is equivalent to four BFS checks from base vertices at the
# identity element, because left translation by G is an automorphism.
# A voltage search (annealing over darts) minimises unreached pairs.
# ---------------------------------------------------------------------------

def _lift2_edges(N, MT, darts):
    edges = []
    for a, b, g in darts:
        for x in range(N):
            edges.append((a * N + x, (2 + b) * N + MT[x][g]))
    return 4 * N, edges


def _lift2_cost(N, MT, darts):
    """Sum over the four base sources of vertices NOT within distance 3."""
    n = 4 * N
    adj = [[] for _ in range(n)]
    for a, b, g in darts:
        for x in range(N):
            u = a * N + x
            v = (2 + b) * N + MT[x][g]
            adj[u].append(v)
            adj[v].append(u)
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(3):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
        total += n - count
    return total


def _lift2_search(N, MT, d, rng, deadline, steps):
    """Anneal voltages of the 2x2 base lift; return list of (a, b, g) darts or None."""
    t = rng.randrange(1, d)
    counts = [(0, 0, t), (0, 1, d - t), (1, 0, d - t), (1, 1, t)]
    darts = []
    used = {}
    for a, b, c in counts:
        S = rng.sample(range(N), c)
        used[(a, b)] = set(S)
        for g in S:
            darts.append([a, b, g])
    cur = _lift2_cost(N, MT, darts)
    for k in range(steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        T = 1.5 * (1.0 - k / steps) + 0.05
        i = rng.randrange(len(darts))
        a, b, old = darts[i]
        g = rng.randrange(N)
        if g in used[(a, b)]:
            continue
        darts[i][2] = g
        new = _lift2_cost(N, MT, darts)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            used[(a, b)].discard(old)
            used[(a, b)].add(g)
            cur = new
        else:
            darts[i][2] = old
    if cur == 0:
        return [tuple(x) for x in darts]
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

    # Stage 1: difference-cover group lifts (order 2N), limited budget.
    try:
        now = time.monotonic()
        stage1_deadline = now + 0.4 * max(0.0, deadline - now)
        hi = d * (d - 1) + 1
        lo = max(best_n // 2 + 1, d)
        for N in range(lo, hi + 1):
            if time.monotonic() >= stage1_deadline:
                break
            if 2 * N <= best_n:
                continue
            groups = _group_list(N, rng)
            tables = [None] * len(groups)
            found = None
            deadline_N = time.monotonic() + 0.5 * max(0.0, stage1_deadline - time.monotonic())
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
    except Exception:
        pass

    # Stage 2: 2x2 base group lifts (order 4N), new construction.
    try:
        moore = lib.moore_bound(d, D)
        N = best_n // 4 + 1
        while time.monotonic() < deadline and 4 * N <= moore:
            groups = _group_list(N, rng)
            tables = [None] * len(groups)
            found = None
            now = time.monotonic()
            deadline_N = now + 0.6 * max(0.0, deadline - now)
            while found is None and time.monotonic() < deadline_N:
                for idx in range(len(groups)):
                    if time.monotonic() >= deadline_N:
                        break
                    if tables[idx] is None:
                        mul, inv = groups[idx][1], groups[idx][2]
                        tables[idx] = _tables_pair(N, mul, inv)
                    MT, _IV = tables[idx]
                    darts = _lift2_search(N, MT, d, rng, deadline_N, 3000)
                    if darts is not None:
                        found = (MT, darts)
                        break
            if found is None:
                break
            MT, darts = found
            try:
                n, edges = _lift2_edges(N, MT, darts)
                consider(n, edges)
            except Exception:
                pass
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best


def _tables_pair(N, mul, inv):
    """Multiplication table and inverse list for a group of order N."""
    MT = [[mul(x, y) for y in range(N)] for x in range(N)]
    IV = [inv(x) for x in range(N)]
    return MT, IV
