import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------

MAX_GROUPS = 12        # semidirect groups tried per order N in one bi-Cayley attempt
CLIMB_ITERS = 1500     # hill-climb steps per restart
STALL_LIMIT = 300      # re-randomize after this many non-improving steps
N_WINDOW = 8           # semidirect bi-Cayley orders tried just above the record
PERM_PROB = 0.6        # probability of using a permutation-group lift per step
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Baseline constructions (D = 3 and D = 4 families).
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW: permutation groups from generators on the projective line.
#
# PSL(2,p) and PGL(2,p) act on the p+1 points of the projective line. Taking a
# direct product with a cyclic group Z_c (acting on c extra points) gives many
# non-metacyclic groups, e.g. PSL(2,7) (order 168), PGL(2,7) (order 336),
# A5 x Z_3 (order 180). These are exactly the orders the semidirect family
# cannot reach. The closure is computed by BFS, and the group is then used as
# a bi-Cayley lift: A_x ~ B_{x g} for g in S, with identity at index 0.
# ----------------------------------------------------------------------------

def _proj_gens(p, pgl, c):
    """Generators (as permutations of p+1+c points) of PSL/PGL(2,p) x Z_c."""
    inf = p
    npts = p + 1 + c

    def lift(f):
        perm = list(range(npts))
        for x in range(p + 1):
            perm[x] = f(x)
        return tuple(perm)

    def t(x):
        return inf if x == inf else (x + 1) % p

    def s(x):
        if x == inf:
            return 0
        if x == 0:
            return inf
        return (-pow(x, p - 2, p)) % p

    gens = [lift(t), lift(s)]
    if pgl:
        nons = next(v for v in range(2, p) if pow(v, (p - 1) // 2, p) == p - 1)

        def u(x):
            if x == inf or x == 0:
                return x
            return (nons * x) % p

        gens.append(lift(u))
    if c >= 2:
        z = list(range(npts))
        for i in range(c):
            z[p + 1 + i] = p + 1 + (i + 1) % c
        gens.append(tuple(z))
    return gens, npts


def _closure(gens, npts, cap):
    """BFS closure of generators; returns (elements, index) with identity at index 0, or None if > cap."""
    ident = tuple(range(npts))
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(g[t] for t in x)
            if y not in index:
                if len(elems) >= cap:
                    return None
                index[y] = len(elems)
                elems.append(y)
    return elems, index


def _perm_tables(elems, index):
    """Multiplication table T[x][g] = x*g and inverse table for a permutation group."""
    N = len(elems)
    T = []
    for a in elems:
        T.append([index[tuple(b[t] for t in a)] for b in elems])
    invs = [0] * N
    for x in range(N):
        row = T[x]
        for g in range(N):
            if row[g] == 0:
                invs[x] = g
                break
    return T, invs


def _perm_candidates(lo, hi, d):
    """Bi-Cayley-usable permutation groups of order N in [lo, hi] with N > d."""
    out = []
    for p in (3, 5, 7):
        for pgl in (False, True):
            for c in range(1, 7):
                gens, npts = _proj_gens(p, pgl, c)
                cl = _closure(gens, npts, hi + 1)
                if cl is None:
                    continue
                elems, index = cl
                N = len(elems)
                if N < lo or N > hi or N <= d:
                    continue
                T, invs = _perm_tables(elems, index)
                out.append((N, T, invs))
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley lifts (shared search, any group given by table T and inverses).
# Vertices A_x, B_y for x, y in G; A_x ~ B_{x g} for g in S, |S| = d.
# Identity is index 0 and WLOG in S. Left translation is an automorphism,
# so eccentricities from A_0 and B_0 decide the diameter.
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


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D, cap=None):
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
        if cap is not None and total > cap:
            return total
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb S to zero unreached pairs; sideways moves allowed; restarts on stall."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
    stall = 0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D, cap=cur)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Try several semidirect groups of order N; return (T, S) for the first valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and meets the Moore bound 2d for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured baselines.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # NEW: pre-build permutation groups of orders that the semidirect family misses.
    lo0 = best_n // 2 + 1
    hi0 = moore // 2
    perm_cands = []
    if lo0 <= hi0 and time.monotonic() < deadline:
        perm_cands = _perm_candidates(lo0, hi0, d)

    # Main search: beat the current best order.
    while best_n < moore and time.monotonic() < deadline:
        lo = best_n // 2 + 1
        if lo > moore // 2:
            break

        if perm_cands and rng.random() < PERM_PROB:
            usable = [c for c in perm_cands if c[0] >= lo]
            if usable:
                N, T, invs = rng.choice(usable)
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
                continue

        # Semidirect bi-Cayley lift of order N; the lift has 2N vertices.
        N = lo + rng.randrange(N_WINDOW)
        if N <= d:
            continue
        res = _search_bicayley(d, D, N, rng, deadline)
        if res is not None:
            T, S = res
            consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
