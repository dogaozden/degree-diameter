import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe base constructions.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _gq_base(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bipartite Cayley (Haar-type) graphs over small non-abelian groups.
#
# Vertices a_x = x and b_y = G + y for x, y in Z: a_x ~ b_y iff x^{-1} y in S,
# with |S| = d. Left multiplication is an automorphism that is transitive on
# each side, so diameter <= D holds iff BFS of depth D from a_e and from b_e
# reaches every vertex.
# ----------------------------------------------------------------------------

def _random_group(G, rng):
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    k = rng.choice(divs)
    m = G // k
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        return lib.semidirect_group(m, k, r)
    except ValueError:
        return None


def _cost(G, S, T, invt, D):
    """Number of (source, target) unreached vertices from a_e and b_e within depth D."""
    Sinv = [invt[s] for s in S]
    N2 = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N2)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = T[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - G]
                    for si in Sinv:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N2 - cnt
    return total


def _anneal(G, d, D, T, invt, rng, end):
    S = rng.sample(range(G), d)
    cost = _cost(G, S, T, invt, D)
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    while cost > 0 and time.monotonic() < end:
        frac = (time.monotonic() - t0) / span
        temp = max(0.2, 2.0 * (1.0 - frac))
        i = rng.randrange(d)
        g = rng.randrange(G)
        if g in S:
            continue
        old = S[i]
        S[i] = g
        c2 = _cost(G, S, T, invt, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
        else:
            S[i] = old
    return list(S) if cost == 0 else None


def _group_search(d, D, deadline, rng, consider, best_n):
    hi = lib._moore_bound(d, D) // 2
    lo = best_n // 2 + 1
    if lo > hi:
        return
    lo_s = min(hi, max(lo, (7 * hi) // 10))
    hi_s = min(hi, max(lo_s, lo + 40))
    while time.monotonic() < deadline:
        G = rng.randint(lo_s, hi_s)
        g = _random_group(G, rng)
        if g is None:
            continue
        order, mul, inv = g
        T = [[mul(x, y) for y in range(order)] for x in range(order)]
        invt = [inv(x) for x in range(order)]
        slice_end = min(deadline, time.monotonic() + 3.0)
        S = _anneal(order, d, D, T, invt, rng, slice_end)
        if S is not None:
            edges = [(x, order + T[x][s]) for x in range(order) for s in S]
            consider(2 * order, edges)


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

    st = [lib.haar_graph(d, range(d))]  # K_{d,d}: valid fallback for D >= 2

    def consider(n, e):
        if n > st[0][0] and lib.is_valid(n, e, d, D):
            st[0] = (n, e)

    try:
        if D == 2:
            pass
        elif d == 2:
            n = 2 * D
            consider(n, [(i, (i + 1) % n) for i in range(n)])
        else:
            if D == 3 and lib.is_prime_power(d - 1):
                consider(*lib.projective_plane_incidence(d - 1))
            if D >= 4:
                b = _gq_base(d)
                if b is not None:
                    consider(*b)
            if d >= 3 and st[0][0] < lib._moore_bound(d, D):
                _group_search(d, D, deadline, rng, consider, st[0][0])
    except Exception:
        pass

    n, e = st[0]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
