import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: PG(2, q) for D = 3 and the generalized quadrangle W(q) for D >= 4.
# ----------------------------------------------------------------------------

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


def _pp_below(x):
    """Largest prime power <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# ----------------------------------------------------------------------------
# New construction: bi-Cayley graphs over finite groups.
#
# Vertices a_x and b_y for x, y in G (|G| = m). Connection set S of size d gives
# edges a_x ~ b_{x s} for s in S. Left multiplication is an automorphism, so the
# diameter is at most D iff BFS of depth D from a_1 and from b_1 reaches everything.
# We search S by simulated-annealing-style local search minimising unreached pairs.
# ----------------------------------------------------------------------------

def _semidirect_specs(m):
    """Parameters (a, k, r) of nontrivial semidirect products Z_a x| Z_k of order m."""
    specs = []
    for a in range(2, m):
        if m % a:
            continue
        k = m // a
        if k < 2:
            continue
        for r in range(2, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                specs.append((a, k, r))
    return specs


def _tables(m, spec):
    """Multiplication table T and inverse list INV for the group of order m given by spec (None = cyclic)."""
    if spec is None:
        _, mul, inv = lib.cyclic_group(m)
    else:
        a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    T = [[mul(x, y) for y in range(m)] for x in range(m)]
    INV = [inv(x) for x in range(m)]
    return T, INV


def _unreached(m, T, S, Sinv, D, src):
    """Number of vertices of the bi-Cayley graph not within distance D of vertex src."""
    n = 2 * m
    seen = bytearray(n)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < m:
                row = T[v]
                for s in S:
                    w = m + row[s]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                row = T[v - m]
                for si in Sinv:
                    w = row[si]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return n - cnt


def _cost(m, T, INV, S, D):
    Sinv = [INV[s] for s in S]
    return _unreached(m, T, S, Sinv, D, 0) + _unreached(m, T, S, Sinv, D, m)


def _anneal(m, T, INV, d, D, deadline, rng):
    """Local search for a d-element connection set with cost 0; returns S or None."""
    S = rng.sample(range(m), d)
    cur = _cost(m, T, INV, S, D)
    best_seen = cur
    stall = 0
    while True:
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        g = rng.randrange(m)
        if g in S:
            continue
        S2 = S[:]
        S2[i] = g
        c2 = _cost(m, T, INV, S2, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / 0.7):
            S, cur = S2, c2
        if cur < best_seen:
            best_seen = cur
            stall = 0
        else:
            stall += 1
            if stall > 2500:
                S = rng.sample(range(m), d)
                cur = _cost(m, T, INV, S, D)
                best_seen = cur
                stall = 0


def _bicayley_scan(best, d, D, moore, deadline, rng):
    """Scan per-side orders m upward from the current best, returning the best valid graph found."""
    M = moore // 2
    m = best[0] // 2 + 1
    fails = 0
    while m <= M and time.monotonic() < deadline and fails < 3:
        now = time.monotonic()
        remaining = deadline - now
        budget_end = now + max(0.5, remaining * 0.35)
        specs = [None] + rng.sample(_semidirect_specs(m), min(3, len(_semidirect_specs(m))))
        found = None
        for idx, spec in enumerate(specs):
            now = time.monotonic()
            if now >= budget_end:
                break
            sub_end = now + (budget_end - now) / (len(specs) - idx)
            T, INV = _tables(m, spec)

            def mulf(x, g, T=T):
                return T[x][g]

            S = _anneal(m, T, INV, d, D, sub_end, rng)
            if S is None:
                continue
            n2, e2 = lib.group_lift(2, [(0, 1, s) for s in S], m, mulf)
            if lib.is_valid(n2, e2, d, D):
                found = (n2, e2)
                break
        if found is not None:
            best = found
            m = found[0] // 2 + 1
            fails = 0
        else:
            m += 1
            fails += 1
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured base graphs.
    if D == 3:
        q = _pp_below(d - 1)
        if q is not None:
            consider(*lib.projective_plane_incidence(q))
    elif D >= 4:
        q = _pp_below(min(d - 1, 7))
        if q is not None:
            consider(*_gq_w(q))

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Bi-Cayley search for a larger graph; any failure keeps the best verified graph.
    if d >= 3 and time.monotonic() < deadline:
        try:
            best = _bicayley_scan(best, d, D, moore, deadline, rng)
        except Exception:
            pass

    return best
