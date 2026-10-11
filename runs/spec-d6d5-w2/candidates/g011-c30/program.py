import itertools
import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baseline families (cheap, always valid when they apply).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (small q only, for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW PRIMARY FAMILY: bi-Cayley (Haar-type) graphs over small non-abelian groups.
#
# Group G of order N (semidirect Z_m x| Z_k). Vertices L_g and R_h, g, h in G.
# Edge L_g -- R_{g s} for each s in S, |S| = d (distinct).
# Left multiplication by G is an automorphism, so only two BFS sources (L_e and
# R_e) are needed to certify diameter <= D. Degree is exactly d, bipartite.
# ----------------------------------------------------------------------------

def _divisors_groups(N, rng, max_groups):
    """Sample semidirect-product parameters (m, k, r) with m * k = N."""
    pool = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            pool.append((1, k, 1))
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        for r in rng.sample(rs, min(len(rs), 2)):
            pool.append((m, k, r))
        pool.append((m, k, 1))
    rng.shuffle(pool)
    return pool[:max_groups]


class _HaarCtx:
    """Group multiplication with cached right-multiplication permutations."""

    def __init__(self, N, mul, inv):
        self.N = N
        self.mul = mul
        self.inv = inv
        self.cache = {}

    def perms(self, s):
        p = self.cache.get(s)
        if p is None:
            N, mul = self.N, self.mul
            si = self.inv(s)
            fwd = [mul(g, s) for g in range(N)]        # L_g -> R_{g s}
            bwd = [mul(h, si) for h in range(N)]       # R_h -> L_{h s^-1}
            p = (fwd, bwd)
            self.cache[s] = p
        return p


def _haar_cost(ctx, S, D):
    """Number of (source, vertex) pairs at distance > D from L_e and R_e. Zero means valid."""
    N = ctx.N
    P = [ctx.perms(s) for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    for fwd, _b in P:
                        v = N + fwd[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - N
                    for _f, bwd in P:
                        v = bwd[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _haar_search(ctx, d, D, rng, deadline):
    """Simulated-annealing search for a connection set S of d distinct group elements."""
    N = ctx.N
    if N < d:
        return None
    S = rng.sample(range(N), d)
    cur = _haar_cost(ctx, S, D)
    best_c, best_S = cur, list(S)
    while cur > 0:
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c = _haar_cost(ctx, S, D)
        if c <= cur or rng.random() < math.exp(-(c - cur)):
            cur = c
            if c < best_c:
                best_c, best_S = c, list(S)
        else:
            S[i] = old
    return list(best_S) if best_c == 0 else None


def _haar_graph(ctx, S):
    N = ctx.N
    E = []
    for s in S:
        fwd, _ = ctx.perms(s)
        for g in range(N):
            E.append((g, N + fwd[g]))
    return 2 * N, E


def _try_order(N, d, D, rng, deadline):
    groups = _divisors_groups(N, rng, 3)
    for idx, (m, k, r) in enumerate(groups):
        now = time.monotonic()
        if now >= deadline:
            break
        gd = now + (deadline - now) / (len(groups) - idx)
        order, mul, inv = lib.semidirect_group(m, k, r)
        ctx = _HaarCtx(order, mul, inv)
        S = _haar_search(ctx, d, D, rng, gd)
        if S is not None:
            return _haar_graph(ctx, S)
    return None


def _haar_phase(d, D, moore, rng, deadline, consider, best_n):
    """Ascending ladder over group orders N; retries a window with growing budgets."""
    budget = 0.8
    while time.monotonic() < deadline:
        floor_n = int(0.43 * moore / 2)
        lo = max(d, floor_n, best_n() // 2 + 1)
        top = min(moore // 2, lo + max(40, lo // 5))
        if lo > top:
            return
        hit = False
        for N in range(lo, top + 1):
            now = time.monotonic()
            if now >= deadline:
                return
            res = _try_order(N, d, D, rng, min(deadline, now + budget))
            if res is not None:
                consider(res[0], res[1])
                hit = True
                break
        if not hit:
            budget *= 2.0


# ----------------------------------------------------------------------------
# Secondary family: voltage lifts over semidirect products with k base orbits.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(80):
        k2 = rng.choice(choices)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _lift_cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = _random_darts(d, k, G, rng)
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            old_p = perms[idx]
            darts[idx][2] = new
            perms[idx] = _right_perm(mul, G, new)
            c2 = _lift_cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _lift_cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _lift_phase(d, D, rng, deadline, consider, best_n):
    ks = [1, 1, 2, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n() // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(3, lo // 8)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        now = time.monotonic()
        res = _lift_anneal(d, D, k, order, mul, rng,
                           min(deadline, now + 5.0), 1500)
        if res is not None:
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def best_n():
        return best[0]

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best[0] < moore and d >= 2:
        _haar_phase(d, D, moore, rng, min(deadline, start + 0.5 * time_limit),
                    consider, best_n)
        _lift_phase(d, D, rng, deadline, consider, best_n)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
