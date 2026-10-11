import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines for D = 3 and D = 4 (kept from the parent program).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley graphs over FINITE PERMUTATION GROUPS (non-abelian,
# non-semidirect groups such as PSL(2,7), PGL(2,7), A5 x Z_k, S4 x Z_k,
# AGL(1,p)). A_x ~ B_{x s} for s in S, |S| = d, so the graph is d-regular on
# 2N vertices. Search over S by simulated annealing on the number of pairs
# not within distance D, checked from A_e and B_e (left translations are
# automorphisms).
# ----------------------------------------------------------------------------

CLIMB_ITERS = 1000
_GROUP_CACHE = {}
_BASE_ORDER = {'A4': 12, 'S4': 24, 'A5': 60, 'S5': 120}
_MAX_ORDER = 341  # Moore bound 682 = 2 * 341 for d = 5, D = 5; caps every group


def _embed(perm, offset, total):
    """Embed a permutation of a block of points into a larger point set."""
    p = list(range(total))
    for i, x in enumerate(perm):
        p[offset + i] = offset + x
    return tuple(p)


def _cyc(n):
    """The n-cycle on n points."""
    return tuple((i + 1) % n for i in range(n))


def _base_gens(name):
    """Generators (as tuples) of a small permutation group, with its point count."""
    if name == 'A4':
        return 4, [(1, 2, 0, 3), (1, 0, 3, 2)]
    if name == 'S4':
        return 4, [(1, 0, 2, 3), (1, 2, 3, 0)]
    if name == 'A5':
        return 5, [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]
    if name == 'S5':
        return 5, [(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)]
    raise ValueError(name)


def _line_gens(pgl):
    """Generators of PSL(2,7) (or PGL(2,7)) acting on the projective line {0..6, inf=7}."""
    inv = {1: 1, 2: 4, 3: 5, 4: 2, 5: 3, 6: 6}
    gens = [
        tuple([(x + 1) % 7 for x in range(7)] + [7]),        # x -> x + 1
        tuple([(2 * x) % 7 for x in range(7)] + [7]),        # x -> 2x (2 is a square)
        tuple([7] + [(-inv[x]) % 7 for x in range(1, 7)] + [0]),  # x -> -1/x
    ]
    if pgl:
        gens.append(tuple([(3 * x) % 7 for x in range(7)] + [7]))  # x -> 3x (non-square)
    return gens


def _prim_root(p):
    """A primitive root modulo the prime p."""
    for g in range(2, p):
        x, seen = 1, set()
        for _ in range(p - 1):
            x = x * g % p
            seen.add(x)
        if len(seen) == p - 1:
            return g
    return 1


def _key_gens(key):
    """Return (point_count, generators) for a named group key, or None."""
    kind = key[0]
    if kind == 'pgl27':
        return 8, _line_gens(True)
    if kind == 'psl27':
        return 8, _line_gens(False)
    if kind == 'agl':
        p = key[1]
        g = _prim_root(p)
        return p, [tuple((x + 1) % p for x in range(p)),
                   tuple((g * x) % p for x in range(p))]
    if kind == 'pslx':
        k = key[1]
        total = 8 + k
        gens = [_embed(g, 0, total) for g in _line_gens(False)]
        if k >= 2:
            gens.append(_embed(_cyc(k), 8, total))
        return total, gens
    if kind == 'prod':
        base, k = key[1], key[2]
        b, bg = _base_gens(base)
        total = b + k
        gens = [_embed(g, 0, total) for g in bg]
        if k >= 2:
            gens.append(_embed(_cyc(k), b, total))
        return total, gens
    return None


def _closure(gens, total, limit):
    """All elements of the group generated by gens (identity first); None if above limit."""
    idp = tuple(range(total))
    elems = [idp]
    idx = {idp: 0}
    frontier = [idp]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[v] for v in x)
                if y not in idx:
                    if len(elems) >= limit:
                        return None
                    idx[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return elems, idx


def _tables(elems, idx, total):
    """T[x][g] = index of x*g (composition), and invs[g] = index of g^-1."""
    T = []
    for a in elems:
        T.append([idx[tuple(a[x] for x in b)] for b in elems])
    invs = []
    for g in elems:
        inv = [0] * total
        for i, gi in enumerate(g):
            inv[gi] = i
        invs.append(idx[tuple(inv)])
    return T, invs


def _cache_put(key, val):
    if len(_GROUP_CACHE) >= 8:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[key] = val


def _build_group(key):
    """(N, T, invs) for a named permutation group, or None if it is out of range."""
    if key in _GROUP_CACHE:
        return _GROUP_CACHE[key]
    res = None
    spec = _key_gens(key)
    if spec is not None:
        total, gens = spec
        cl = _closure(gens, total, _MAX_ORDER)
        if cl is not None:
            elems, idx = cl
            T, invs = _tables(elems, idx, total)
            res = (len(elems), T, invs)
    _cache_put(key, res)
    return res


def _candidate_keys(hi):
    """Named groups with approximate orders (verified after construction)."""
    out = [(('pgl27',), 336), (('psl27',), 168), (('agl', 13), 156),
           (('agl', 17), 272), (('pslx', 2), 336)]
    for base in ('A4', 'S4', 'A5', 'S5'):
        for k in range(1, 30):
            order = _BASE_ORDER[base] * k
            if order > hi:
                break
            out.append((('prod', base, k), order))
    return out


# ----------------------------------------------------------------------------
# Cyclic-free semidirect groups from lib, used as a secondary source.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _semidirect_pick(lo, hi, rng):
    """(N, T, invs) for a random semidirect group with order in [lo, hi]."""
    N = rng.randint(lo, min(hi, lo + max(2, lo // 10)))
    opts = _groups(N)
    if not opts:
        return None
    m, k, r = rng.choice(opts)
    key = ('sd', m, k, r)
    if key in _GROUP_CACHE:
        return _GROUP_CACHE[key]
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    res = (order, T, invs)
    _cache_put(key, res)
    return res


# ----------------------------------------------------------------------------
# Bi-Cayley search: annealing over the connection set S (identity fixed in S).
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, sources A_0 and B_0."""
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
    """Simulated annealing over S; returns S if all pairs are within distance D."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    hi = min(moore // 2, _MAX_ORDER)
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > hi:
            break

        built = None
        if rng.random() < 0.6:
            cands = [key for key, order in _candidate_keys(hi) if lo <= order <= hi]
            if cands:
                built = _build_group(rng.choice(cands))
        if built is None:
            built = _semidirect_pick(lo, hi, rng)
        if built is None:
            continue

        N, T, invs = built
        if N < lo or N > hi or N < d:
            continue
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
