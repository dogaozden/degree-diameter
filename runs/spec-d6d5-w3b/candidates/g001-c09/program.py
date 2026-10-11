import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Classical families used as fallbacks: projective plane, Araujo-Pardo-Lopez
# for D = 3, generalized quadrangle W(q) for D >= 4, and K_{d,d} / cycles.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
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
    """W(q) for the largest prime power q with q + 1 <= d, capped for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley graphs over non-abelian groups Z_m x| Z_k.
#
# Vertices A_x and B_y for x, y in G (|G| = N). Connection set S of size d:
# A_x is joined to B_{x s} for s in S. Left multiplication by g is an
# automorphism, so the graph is vertex-transitive on each side. Hence the
# diameter is at most D iff the eccentricities of A_e and B_e are at most D.
# Two BFS runs therefore decide validity. The search hill-climbs over S
# for groups whose order is just above the record half-order.
# ----------------------------------------------------------------------------

def _bc_cost(N, pairs, D, limit=float("inf")):
    """Unreached (vertex, source) count from A_e and B_e within distance D. Zero means valid."""
    N2 = 2 * N
    total = 0
    for src in (0, N):
        seen = bytearray(N2)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    for perm, _invp in pairs:
                        v = N + perm[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    y = u - N
                    for _perm, invp in pairs:
                        v = invp[y]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            if not nxt:
                break
            frontier = nxt
        total += N2 - count
        if total > limit:
            return total
    return total


def _climb(d, D, N, mul, inv, rng, deadline, iters):
    """Hill-climb a size-d connection set S in the group of order N. Returns (S or None, cost)."""
    cache = {}

    def pair(s):
        p = cache.get(s)
        if p is None:
            si = inv(s)
            p = ([mul(x, s) for x in range(N)], [mul(y, si) for y in range(N)])
            cache[s] = p
        return p

    S = rng.sample(range(N), d)
    cur = _bc_cost(N, [pair(s) for s in S], D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        T = S[:]
        T[i] = t
        c = _bc_cost(N, [pair(s) for s in T], D, limit=cur)
        if c <= cur:
            S, cur = T, c
    return (S if cur == 0 else None), cur


def _bicayley_edges(N, mul, S):
    """Edges of the bi-Cayley graph: A_x (index x) joined to B_{x s} (index N + x s)."""
    return [(x, N + mul(x, s)) for s in S for x in range(N)]


# ----------------------------------------------------------------------------
# Top level.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.82 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if d == 2:
            n = 2 * D
            consider(n, [(i, (i + 1) % n) for i in range(n)])

        if D >= 3 and d >= 3:
            try:
                pg = _best_pg(d)
                if pg is not None:
                    consider(pg[0], pg[1])
            except Exception:
                pass
            try:
                ar = _araujo(d)
                if ar is not None:
                    consider(ar[0], ar[1])
            except Exception:
                pass

        if D >= 4 and d >= 3:
            try:
                gq = _best_gq(d)
                if gq is not None:
                    consider(gq[0], gq[1])
            except Exception:
                pass

        # Main new family: bi-Cayley graphs over Z_m x| Z_k.
        if d >= 3 and D >= 2:
            moore = lib.moore_bound(d, D)
            Nmax = moore // 2
            while time.monotonic() < deadline and best_n < 2 * Nmax:
                lo = max(d, best_n // 2 + 1)
                if lo > Nmax:
                    break
                hi = min(Nmax, lo + max(3, lo // 16))
                N = rng.randint(lo, hi)
                ks = [k for k in range(1, N + 1) if N % k == 0 and N // k >= 2]
                if not ks:
                    continue
                nonab = [k for k in ks if k >= 2]
                if nonab and rng.random() < 0.8:
                    k = rng.choice(nonab)
                else:
                    k = 1
                m = N // k
                if k == 1:
                    r = 1
                else:
                    cands = [r for r in range(1, m)
                             if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
                    if not cands:
                        continue
                    r = rng.choice(cands)
                try:
                    order, mul, inv = lib.semidirect_group(m, k, r)
                except ValueError:
                    continue
                if order < d:
                    continue
                S, _c = _climb(d, D, order, mul, inv, rng, deadline, 400)
                if S is not None:
                    consider(2 * order, _bicayley_edges(order, mul, S))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
