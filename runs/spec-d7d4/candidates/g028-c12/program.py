import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4, degree q+1).
# Used only as a fallback base when d-1 is a prime power.
# ----------------------------------------------------------------------------

def _gq_w(q):
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
# Bipartite Z_b-layered voltage lifts over small groups, found by annealing.
#
# Base: b "A" vertices and b "B" vertices, and d layers. Layer l is a
# permutation p_l of range(b) with voltages g_{l,i} in the group G of order m.
# Dart (i, p_l(i), g_{l,i}) lifts to edges A(i,x) -- B(p_l(i), x*g) for all x.
# Left translation by h is an automorphism, so distances only need to be
# checked from the 2b representatives A(i,e) and B(j,e). The cost is the
# number of (representative, vertex) pairs at distance > D; zero means valid.
# ----------------------------------------------------------------------------

def _groups(m):
    """Return (a, k, r) triples giving groups of order m (cyclic first)."""
    opts = [(m, 1, 1)]
    for k in range(2, m + 1):
        if m % k:
            continue
        a = m // k
        if a < 2:
            continue
        for r in range(2, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
                opts.append((a, k, r))
    return opts


def _lift_adj(L, b, m, mt):
    boff = b * m
    adj = [[] for _ in range(2 * boff)]
    for p, gv in L:
        for i in range(b):
            j = p[i]
            g = gv[i]
            base_a = i * m
            base_b = boff + j * m
            for x in range(m):
                a = base_a + x
                y = base_b + mt[x][g]
                adj[a].append(y)
                adj[y].append(a)
    return adj


def _bad(adj, N, D, sources):
    bad = 0
    for s in sources:
        seen = bytearray(N)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nf = []
            for v in frontier:
                for u in adj[v]:
                    if not seen[u]:
                        seen[u] = 1
                        nf.append(u)
            if not nf:
                break
            cnt += len(nf)
            frontier = nf
        bad += N - cnt
    return bad


def _anneal(b, m, d, D, mt, deadline, rng):
    """Anneal layers until every representative reaches all vertices within D. Returns layers or None."""
    boff = b * m
    N = 2 * boff
    sources = [i * m for i in range(b)] + [boff + j * m for j in range(b)]
    L = []
    for _ in range(d):
        p = rng.sample(range(b), b)
        gv = [rng.randrange(m) for _ in range(b)]
        L.append((p, gv))
    cur = _bad(_lift_adj(L, b, m, mt), N, D, sources)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while True:
        if cur == 0:
            return L
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 0.8 * (1 - (now - t0) / span) + 0.03
        l = rng.randrange(d)
        i = rng.randrange(b)
        p2 = [(pp[:], gg[:]) for pp, gg in L]
        if b > 1 and rng.random() < 0.4:
            pp = p2[l][0]
            k = rng.randrange(b)
            pp[i], pp[k] = pp[k], pp[i]
        else:
            p2[l][1][i] = rng.randrange(m)
        new = _bad(_lift_adj(p2, b, m, mt), N, D, sources)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            L, cur = p2, new


def _lift_edges(L, b, m, mt):
    boff = b * m
    es = set()
    for p, gv in L:
        for i in range(b):
            j = p[i]
            g = gv[i]
            for x in range(m):
                es.add((i * m + x, boff + j * m + mt[x][g]))
    return sorted(es)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = None

    def consider(n, e):
        nonlocal best
        if (best is None or n > best[0]) and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Safe fallback: K_{d,d}, diameter 2.
    consider(*lib.haar_graph(d, range(d)))

    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        if D == 3:
            consider(*lib.projective_plane_incidence(q))
        elif D >= 4:
            consider(*_gq_w(q))

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Lift sweep: try increasing even orders N = 2*b*m just above the current best.
    SLICE = 1.2
    N = best[0] + 2
    while time.monotonic() < deadline and N <= moore:
        configs = [(b, N // (2 * b)) for b in range(1, 7)
                   if N % (2 * b) == 0 and N // (2 * b) >= 2]
        rng.shuffle(configs)
        found = None
        for b, m in configs[:6]:
            if time.monotonic() >= deadline:
                break
            trip = rng.choice(_groups(m))
            _, mul, _ = lib.semidirect_group(*trip)
            mt = [[mul(x, y) for y in range(m)] for x in range(m)]
            sl = min(deadline, time.monotonic() + SLICE)
            L = _anneal(b, m, d, D, mt, sl, rng)
            if L is not None:
                edges = _lift_edges(L, b, m, mt)
                if lib.is_valid(2 * b * m, edges, d, D):
                    found = (2 * b * m, edges)
                    break
        if found is not None and found[0] > best[0]:
            best = found
        N += 2

    return best
