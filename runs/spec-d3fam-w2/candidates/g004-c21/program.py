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


def _parent(d, rng, deadline):
    """Previous strategy: Araujo-Pardo for d = q+2, then difference-cover Haar lifts."""
    best = _fallback(d, 3)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, 3):
            best = (n, e)
            best_n = n

    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

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


# ---- New strategy: annealed voltage lifts of a k+k base multigraph over Z_N ----

def _cost(k, N, P, g):
    """Number of ordered vertex pairs at distance > 3, plus a penalty for duplicate darts."""
    n = 2 * k * N
    base = k * N
    adj = [[] for _ in range(n)]
    for (a, b), gv in zip(P, g):
        ao = a * N
        bo = base + b * N
        for x in range(N):
            u = ao + x
            v = bo + (x + gv) % N
            adj[u].append(v)
            adj[v].append(u)
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    bad = n * n - sum(r.bit_count() for r in reach)
    conflicts = len(P) - len(set((a, b, gv) for (a, b), gv in zip(P, g)))
    return bad + 30 * conflicts


def _lift_search(k, N, d, rng, deadline):
    """Anneal voltages on a k+k base where every vertex has degree d; return (P, g) or None."""
    P = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for a in range(k):
            P.append((a, perm[a]))
    m = len(P)
    g = [rng.randrange(N) for _ in range(m)]
    cur = _cost(k, N, P, g)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = 2.0 * (1.0 - frac) + 0.2
        i = rng.randrange(m)
        old = g[i]
        g[i] = rng.randrange(N)
        new = _cost(k, N, P, g)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            g[i] = old
    if cur == 0:
        return P, g
    return None


def _lift_edges(k, N, P, g):
    n = 2 * k * N
    base = k * N
    edges = []
    for (a, b), gv in zip(P, g):
        for x in range(N):
            edges.append((a * N + x, base + b * N + (x + gv) % N))
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    end = start + total
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    if D != 3 or d < 3:
        return best

    if lib.is_prime_power(d - 1):
        cand = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(cand[0], cand[1], d, D):
            return cand
        return best

    # Parent strategy gets a bounded share of the budget; it never lowers the result.
    p = _parent(d, rng, start + 0.4 * total)
    if p[0] > best[0] and lib.is_valid(p[0], p[1], d, D):
        best = p
    best_n = best[0]

    # New strategy: voltage lifts of a k+k base with order 2kN > best_n.
    cands = []
    for k in range(2, 6):
        if k > d:
            continue
        n0 = best_n // (2 * k) + 1
        for N in range(max(n0, d), n0 + 2):
            if 2 * k * N > best_n:
                cands.append((2 * k * N, k, N))
    cands.sort()

    for idx, (order, k, N) in enumerate(cands):
        now = time.monotonic()
        if now >= end:
            break
        slice_end = now + max(0.5, (end - now) / (len(cands) - idx))
        res = _lift_search(k, N, d, rng, min(slice_end, end))
        if res is None:
            continue
        P, g = res
        n, edges = _lift_edges(k, N, P, g)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
            break

    return best
