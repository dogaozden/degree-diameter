import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe base constructions. Each is checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q) (diameter 4)."""
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over non-abelian groups of a prescribed order.
#
# Vertices: A_{i,g} = i*N + g and B_{j,h} = (k+j)*N + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every g.
# Left multiplication is an automorphism, so distances are measured from one
# representative A_{i,e} or B_{j,e} per layer.
#
# Groups: metacyclic Z_m x| Z_k2 (non-abelian only) and direct products of
# two small groups. These are enumerated exhaustively for each target order,
# which goes beyond the single narrow window and families used previously.
# ----------------------------------------------------------------------------

_BIG = 10 ** 6


def _meta_specs(N):
    """Non-abelian metacyclic specs ('meta', m, k2, r) with m * k2 = N. r = 1 is excluded (abelian)."""
    out = []
    for k2 in range(2, N + 1):
        if N % k2:
            continue
        m = N // k2
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append(('meta', m, k2, r))
    return out


def _order_specs(N, rng):
    """Specs of non-abelian groups of order N (metacyclic and direct products)."""
    out = _meta_specs(N)
    for a in range(2, N // 2 + 1):
        if N % a:
            continue
        b = N // a
        A = _meta_specs(a) + [('meta', a, 1, 1)]
        B = _meta_specs(b) + [('meta', b, 1, 1)]
        na_a = {s: (s[0] == 'meta' and s[2] > 1) for s in A}
        na_b = {s: (s[0] == 'meta' and s[2] > 1) for s in B}
        pairs = [(sa, sb) for sa in A for sb in B if na_a[sa] or na_b[sb]]
        rng.shuffle(pairs)
        for sa, sb in pairs[:3]:
            out.append(('prod', sa, sb))
    rng.shuffle(out)
    return out[:80]


def _spec_table(spec):
    """Return (N, T) with T[x][y] = x*y for the group described by spec."""
    if spec[0] == 'meta':
        _, m, k2, r = spec
        N = m * k2
        powers = [pow(r, b, m) for b in range(k2)]
        T = [[0] * N for _ in range(N)]
        for x in range(N):
            a, b = divmod(x, k2)
            row = T[x]
            pb = powers[b]
            for y in range(N):
                c, dd = divmod(y, k2)
                row[y] = ((a + pb * c) % m) * k2 + (b + dd) % k2
        return N, T
    _, s1, s2 = spec
    N1, T1 = _spec_table(s1)
    N2, T2 = _spec_table(s2)
    N = N1 * N2
    T = [[0] * N for _ in range(N)]
    for x in range(N):
        x1, x2 = divmod(x, N2)
        row = T[x]
        for y in range(N):
            y1, y2 = divmod(y, N2)
            row[y] = T1[x1][y1] * N2 + T2[x2][y2]
    return N, T


def _adjacency(k, N, T, D_unused, darts):
    n = 2 * k * N
    adj = [[] for _ in range(n)]
    for i, j, s in darts:
        ai = i * N
        bj = (k + j) * N
        for g in range(N):
            a = ai + g
            b = bj + T[g][s]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _cost(k, N, T, D, darts):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    if len(set(darts)) < len(darts):
        return _BIG
    n = 2 * k * N
    adj = _adjacency(k, N, T, D, darts)
    reps = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(n)
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += n - count
    return total


def _edges(k, N, T, darts):
    E = []
    for i, j, s in darts:
        for g in range(N):
            E.append((i * N + g, (k + j) * N + T[g][s]))
    return 2 * k * N, E


def _random_darts(k, d, N, rng):
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            while True:
                t = (i, p[i], rng.randrange(N))
                if t not in darts:
                    break
            darts.append(t)
    return darts


def _anneal(k, d, N, T, D, rng, deadline, iters):
    """Simulated annealing over dart voltages and layer permutations. Returns darts or None."""
    darts = _random_darts(k, d, N, rng)
    cost = _cost(k, N, T, D, darts)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = 1.5 * (1.0 - it / iters) + 0.05
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            i, j, s = darts[idx]
            ns = rng.randrange(N)
            if ns == s:
                continue
            cand = (i, j, ns)
            if cand in darts:
                continue
            old = darts[idx]
            darts[idx] = cand
            c2 = _cost(k, N, T, D, darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            ta, tb = darts[ia], darts[ib]
            na = (ta[0], tb[1], ta[2])
            nb = (tb[0], ta[1], tb[2])
            if na in darts or nb in darts:
                continue
            darts[ia], darts[ib] = na, nb
            c2 = _cost(k, N, T, D, darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[ia], darts[ib] = ta, tb
    if cost == 0:
        return darts
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.72 * time_limit
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Per-side Moore bound for bipartite graphs of max degree d and diameter D.
    moore_side = sum((d - 1) ** i for i in range(D))
    NMAX = 200

    groups_cache = {}
    ks = [1, 1, 1, 2]

    while time.monotonic() < deadline:
        if best_n >= 2 * moore_side:
            break
        k = rng.choice(ks)
        lo = best_n // (2 * k) + 1
        N = lo + rng.randrange(0, 3)
        if N <= d or N > NMAX or k * N > moore_side:
            continue
        if N not in groups_cache:
            groups_cache[N] = _order_specs(N, rng)
        specs = groups_cache[N]
        if not specs:
            continue
        spec = rng.choice(specs)
        Nn, T = _spec_table(spec)
        darts = _anneal(k, d, Nn, T, D, rng, deadline, iters=1500)
        if darts is not None:
            n, e = _edges(k, Nn, T, darts)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
