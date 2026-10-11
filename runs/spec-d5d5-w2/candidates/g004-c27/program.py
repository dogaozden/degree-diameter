import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baseline: incidence graph of points and lines of W(q), diameter 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over semidirect products Z_m x|_r Z_k.
# A_x ~ B_{x g} for g in S, |S| = d. Left translation is an automorphism, so
# eccentricities from A_0 and B_0 decide diameter for the whole graph.
# ----------------------------------------------------------------------------

_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N and Z_m x|_r Z_k a group."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (T, invs): T[x][g] = x*g, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (T, invs)
    if len(_TABLE_CACHE) >= 32:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _cost(N, T, invs, S, D):
    """Number of ordered pairs (source in {A_0, B_0}, vertex) not within distance D."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb with sideways moves on the connection set S (S[0] = identity WLOG)."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _cost(N, T, invs, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing on the connection set with a cooling schedule."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(N, T, invs, S, D)
    if cur == 0:
        return S
    t_hi, t_lo = 2.0, 0.1
    for it in range(iters):
        if time.monotonic() > deadline:
            break
        temp = t_hi * (t_lo / t_hi) ** (it / max(1, iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _cost(N, T, invs, S, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = v
            if cur == 0:
                return S
        else:
            S[i] = old
    return None


def _edges_bicayley(N, T, S):
    return 2 * N, [(x, N + T[x][g]) for x in range(N) for g in S]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: bipartite, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Generalized quadrangle baseline (diameter 4) when d - 1 is a small prime power.
    if D >= 4 and lib.is_prime_power(d - 1) and d - 1 <= 7:
        gn, ge = _gq_w(d - 1)
        consider(gn, ge)

    # Stage 1: quick hill-climb sweep over bi-Cayley orders to get a strong baseline.
    stage1_end = start + 0.3 * budget
    N = best[0] // 2 + 1
    while best[0] < moore and time.monotonic() < stage1_end:
        N = max(N, best[0] // 2 + 1)
        if 2 * N > moore:
            break
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k2, r in groups[:4]:
            if time.monotonic() > stage1_end:
                break
            T, invs = _tables(m, k2, r)
            S = _climb(N, T, invs, d, D, rng, 200, stage1_end)
            if S is not None:
                consider(*_edges_bicayley(N, T, S))
                break
        N += 1

    # Stage 2: annealed bi-Cayley sweep, always targeting orders above the current best.
    N = best[0] // 2 + 1
    while best[0] < moore and time.monotonic() < deadline:
        N = max(N, best[0] // 2 + 1)
        if 2 * N > moore:
            break
        groups = _groups(N)
        rng.shuffle(groups)
        found = False
        for m, k2, r in groups[:4]:
            if time.monotonic() > deadline:
                break
            T, invs = _tables(m, k2, r)
            S = _anneal(N, T, invs, d, D, rng, 1500, deadline)
            if S is not None:
                consider(*_edges_bicayley(N, T, S))
                found = True
                break
        if not found:
            N += 1
        else:
            N = best[0] // 2 + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
