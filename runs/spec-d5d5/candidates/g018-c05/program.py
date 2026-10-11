import math
import random
import time

import lib

PERM_SPECS = [(3, False), (3, True), (5, False), (5, True), (7, False), (7, True)]
MAX_GROUP_ORDER = 400

_TCACHE = {}
_SPEC_CACHE = {}


# ----------------------------------------------------------------------------
# Group tables. A group of order M is (M, T, invs, e) with T[x][y] = x*y and
# identity index e = 0.
# ----------------------------------------------------------------------------

def _semi_table(m, k, r):
    """Table for Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    M = m * k
    pw = [pow(r, b, m) for b in range(k)]
    els = [divmod(x, k) for x in range(M)]
    T = [[((a + pw[b] * c) % m) * k + (b + dd) % k for (c, dd) in els]
         for (a, b) in els]
    invs = []
    for (a, b) in els:
        nb = (-b) % k
        invs.append(((-pw[nb] * a) % m) * k + nb)
    return M, T, invs, 0


def _prime_divisors(n):
    out, x, f = [], n, 2
    while f * f <= x:
        if x % f == 0:
            out.append(f)
            while x % f == 0:
                x //= f
        f += 1
    if x > 1:
        out.append(x)
    return out


def _prim_root(p):
    if p == 2:
        return 1
    qs = _prime_divisors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in qs):
            return g
    return 1


def _pl_gens(p, full):
    """Generators of PSL(2,p) (full=False) or PGL(2,p) (full=True) on the projective line; infinity = p."""
    g = _prim_root(p)
    t = [(x + 1) % p for x in range(p)] + [p]
    s = [p if x == 0 else (-pow(x, p - 2, p)) % p for x in range(p)] + [0]
    mult = g if full else (g * g) % p
    u = [(mult * x) % p for x in range(p)] + [p]
    return [tuple(t), tuple(s), tuple(u)]


def _perm_table(p, full):
    gens = _pl_gens(p, full)
    s = p + 1
    ident = tuple(range(s))
    elems = [ident]
    idx = {ident: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(g[k] for k in x)
            if y not in idx:
                if len(elems) >= MAX_GROUP_ORDER:
                    return None
                idx[y] = len(elems)
                elems.append(y)
    M = len(elems)
    T = [[idx[tuple(a[k] for k in b)] for b in elems] for a in elems]
    invs = []
    for a in elems:
        inv = [0] * s
        for k, v in enumerate(a):
            inv[v] = k
        invs.append(idx[tuple(inv)])
    return M, T, invs, 0


def _groups_for(M, rng):
    """Candidate group specs of order M (cached)."""
    if M in _SPEC_CACHE:
        return _SPEC_CACHE[M]
    specs = []
    for k in range(1, M + 1):
        if M % k:
            continue
        m = M // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append(('s', m, k, r))
    rng.shuffle(specs)
    specs = specs[:3]
    for p, full in PERM_SPECS:
        order = p * (p * p - 1) // (1 if full else 2)
        if order == M:
            specs.append(('p', p, full))
    if len(_SPEC_CACHE) > 200:
        _SPEC_CACHE.clear()
    _SPEC_CACHE[M] = specs
    return specs


def _table(spec):
    if spec in _TCACHE:
        return _TCACHE[spec]
    if spec[0] == 's':
        _, m, k, r = spec
        tab = _semi_table(m, k, r)
    else:
        tab = _perm_table(spec[1], spec[2])
    if len(_TCACHE) > 60:
        _TCACHE.clear()
    _TCACHE[spec] = tab
    return tab


# ----------------------------------------------------------------------------
# Base-graph lifts. Base: p A-vertices, p B-vertices, d darts per base vertex.
# Dart (a, b, g) lifts to edges (a,x)--(p+b, x*g) for all x in G.
# Vertex id = base*M + x, base in 0..2p-1 (A: 0..p-1, B: p..2p-1).
# Each base class is vertex-transitive under left multiplication, so the
# eccentricity check needs only one source per base class.
# ----------------------------------------------------------------------------

def _random_darts(p, d, M, rng):
    A = [a for a in range(p) for _ in range(d)]
    B = [b for b in range(p) for _ in range(d)]
    rng.shuffle(B)
    darts = []
    for a, b in zip(A, B):
        for _ in range(60):
            g = rng.randrange(M)
            if not any(x[0] == a and x[1] == b and x[2] == g for x in darts):
                break
        else:
            return None
        darts.append([a, b, g])
    return darts


def _cost(p, M, T, invs, darts, D):
    """Total unreached (source, vertex) pairs over one source per base class."""
    outA = [[] for _ in range(p)]
    inB = [[] for _ in range(p)]
    for a, b, g in darts:
        outA[a].append((b, g))
        inB[b].append((a, invs[g]))
    V = 2 * p * M
    total = 0
    for src in range(2 * p):
        seen = bytearray(V)
        seen[src * M] = 1
        frontier = [src * M]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                base, x = divmod(v, M)
                row = T[x]
                if base < p:
                    for b, g in outA[base]:
                        w = (p + b) * M + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    for a, ig in inB[base - p]:
                        w = a * M + row[ig]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(p, M, T, invs, d, D, rng, deadline):
    darts = _random_darts(p, d, M, rng)
    if darts is None:
        return None
    n = len(darts)
    cur = _cost(p, M, T, invs, darts, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        temp = max(0.05, 1.5 * (1.0 - (now - t0) / span))
        cand = [list(x) for x in darts]
        i = rng.randrange(n)
        if rng.random() < 0.5:
            cand[i][2] = rng.randrange(M)
        else:
            j = rng.randrange(n)
            if cand[i][1] == cand[j][1]:
                continue
            cand[i][1], cand[j][1] = cand[j][1], cand[i][1]
        if len({tuple(x) for x in cand}) != n:
            continue
        c = _cost(p, M, T, invs, cand, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            darts, cur = cand, c
    return darts if cur == 0 else None


def _edges(p, M, T, darts):
    edges = []
    for a, b, g in darts:
        for x in range(M):
            edges.append((a * M + x, (p + b) * M + T[x][g]))
    return 2 * p * M, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 8)
    if budget < 1:
        budget = 0.5 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # Fallback: complete bipartite K_{d,d}, diameter 2.
    consider(2 * d, [(i, d + j) for i in range(d) for j in range(d)])

    # Projective plane incidence graph for D = 3.
    if D == 3 and d - 1 >= 2:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break

    if d < 2 or D < 2:
        return best

    mb = lib._moore_bound(d, D)
    if best[0] >= mb:
        return best

    try:
        while time.monotonic() < deadline:
            feasible = [p for p in (1, 2, 3, 4)
                        if best[0] // (2 * p) + 1 <= mb // (2 * p)]
            if not feasible:
                break
            p = rng.choice(feasible)
            lo = best[0] // (2 * p) + 1
            hi = mb // (2 * p)
            if rng.random() < 0.5:
                M = lo + rng.randrange(hi - lo + 1)
            else:
                M = lo + min(hi - lo, int(rng.expovariate(0.2)))
            specs = _groups_for(M, rng)
            if not specs:
                continue
            tab = _table(rng.choice(specs))
            if tab is None:
                continue
            Mm, T, invs, _ = tab
            slice_end = min(deadline, time.monotonic() + 4.0)
            darts = _anneal(p, Mm, T, invs, d, D, rng, slice_end)
            if darts is not None:
                n, e = _edges(p, Mm, T, darts)
                consider(n, e)
                if best[0] >= mb:
                    break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    return best
