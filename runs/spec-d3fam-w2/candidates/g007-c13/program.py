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


# ---------------------------------------------------------------------------
# New construction: multi-orbit group voltage lifts with G-invariant annealing.
#
# Base graph: k A-vertices and k B-vertices, joined by d perfect matchings
# (pi_1, ..., pi_d), giving k*d darts, each with a voltage g in a group G of
# order N. The lift has 2kN vertices (u, x), u in base, x in G, and edge
# (a, x) -- (b, x*g) for each dart (a, b, g). Degree is d everywhere.
#
# Left translation (u, x) -> (u, h*x) is an automorphism, so G is transitive on
# each fibre. Hence the diameter test only needs BFS from the 2k vertices (u, e),
# not from all 2kN vertices. Voltages are annealed to minimise the number of
# (source, target) pairs at distance > D. This generalises Haar lifts (k = 1)
# to lifts with several base orbits, which can reach orders the single-orbit
# difference-cover search does not.
# ---------------------------------------------------------------------------

def _mul_table(N, mul):
    return [[mul(x, y) for y in range(N)] for x in range(N)]


def _lift_adj(k, N, MT, darts):
    adj = [[] for _ in range(2 * k * N)]
    for a, b, g in darts:
        ua = a * N
        vb = (k + b) * N
        for x in range(N):
            u = ua + x
            v = vb + MT[x][g]
            adj[u].append(v)
            adj[v].append(u)
    return adj


def _bad(k, N, D, adj):
    """Number of (source, vertex) pairs with distance > D, sources = (u, identity)."""
    nodes = 2 * k * N
    bad = 0
    for s0 in range(2 * k):
        s = s0 * N
        seen = bytearray(nodes)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        bad += nodes - count
    return bad


def _anneal_lift(k, d, N, MT, D, rng, t_end):
    """Anneal voltages of a k-orbit lift; return the dart list on success, else None."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[a, perms[j][a], rng.randrange(N)] for j in range(d) for a in range(k)]
    cur = _bad(k, N, D, _lift_adj(k, N, MT, darts))
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= t_end:
            break
        T = 0.6 * (1.0 - (now - t0) / span) + 0.02
        t = rng.randrange(len(darts))
        old = darts[t][2]
        new = rng.randrange(N)
        if new == old:
            continue
        darts[t][2] = new
        c = _bad(k, N, D, _lift_adj(k, N, MT, darts))
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            darts[t][2] = old
    return darts if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(1.0, 0.85 * time_limit - 2.0)
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

    # Stage 1: single-orbit difference-cover Haar lifts (k = 1).
    haar_deadline = start + 0.3 * (end - start)
    try:
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

    # Stage 2: multi-orbit voltage lifts (k = 1..4 base pairs), ascending order.
    try:
        moore = lib.moore_bound(d, D)
        cands = []
        for order in range(best_n + 1, moore + 1):
            for k in (1, 2, 3, 4):
                if order % (2 * k) == 0 and order // (2 * k) >= 2:
                    cands.append((order, k, order // (2 * k)))

        group_cache = {}
        for order, k, N in cands:
            now = time.monotonic()
            remaining = end - now
            if remaining < 0.3:
                break
            if order <= best_n:
                continue
            budget_end = now + min(2.5, 0.3 * remaining)
            if N not in group_cache:
                group_cache[N] = [(_mul_table(N, g[1])) for g in _group_list(N, rng)]
            tables = group_cache[N]
            while time.monotonic() < budget_end:
                MT = tables[rng.randrange(len(tables))]
                darts = _anneal_lift(k, d, N, MT, D, rng, budget_end)
                if darts is not None:
                    edges = set()
                    for a, b, g in darts:
                        for x in range(N):
                            edges.add((a * N + x, (k + b) * N + MT[x][g]))
                    consider(2 * k * N, sorted(edges))
                    break
    except Exception:
        pass

    return best
