import itertools
import math
import random
import time

import lib

ITERS = 400          # annealing steps per random start
_TABLES = {}         # cache: (N, m, k, r) -> multiplication table T[x][g]


# ----------------------------------------------------------------------------
# Safe baseline families (cheap; used as the fallback).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: multi-orbit group lifts (a orbits on each side).
#
# Group G = Z_m x| Z_k of order N. Vertices A_{u,x} and B_{v,y} with u,v < a,
# x,y in G. A dart (u, v, g) joins A_{u,x} to B_{v, x*g} for every x in G.
# Every A and B orbit has exactly d darts, so the graph is d-regular-bipartite
# on 2*a*N vertices. Left multiplication is an automorphism, so diameter <= D
# is equivalent to the 2a orbit representatives having eccentricity <= D.
# Search: simulated annealing over the dart set (degree-preserving moves),
# minimizing the number of (representative, vertex) pairs at distance > D.
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


def _table(N, m, k, r):
    """Multiplication table T[x][g] for the group Z_m x|_r Z_k (cached)."""
    key = (N, m, k, r)
    if key not in _TABLES:
        _, mul, _ = lib.semidirect_group(m, k, r)
        _TABLES[key] = [[mul(x, g) for g in range(N)] for x in range(N)]
    return _TABLES[key]


def _cost(a, N, D, T, darts):
    """Number of (orbit representative, vertex) pairs at distance > D."""
    n = 2 * a * N
    nb = [[] for _ in range(n)]
    for u, v, g in darts:
        p0 = u * N
        q0 = (a + v) * N
        for x in range(N):
            p = p0 + x
            q = q0 + T[x][g]
            nb[p].append(q)
            nb[q].append(p)
    # Bit i (i < a) tracks A-representative i; bit a+j tracks B-representative j.
    reach = [0] * n
    for i in range(a):
        reach[i * N] = 1 << i
    for j in range(a):
        reach[(a + j) * N] = 1 << (a + j)
    for _ in range(D):
        new = reach[:]
        for w in range(n):
            acc = reach[w]
            for z in nb[w]:
                acc |= reach[z]
            new[w] = acc
        reach = new
    full = 2 * a
    return sum(full - r.bit_count() for r in reach)


def _init_darts(a, d, N, rng):
    """Random dart multiset with each A orbit and each B orbit used exactly d times."""
    A = [u for u in range(a) for _ in range(d)]
    B = [v for v in range(a) for _ in range(d)]
    rng.shuffle(B)
    darts = []
    for u, v in zip(A, B):
        g = rng.randrange(N)
        for _ in range(50):
            if (u, v, g) not in darts:
                break
            g = rng.randrange(N)
        darts.append((u, v, g))
    if len(set(darts)) != len(darts):
        return None
    return darts


def _sa(a, N, D, T, darts, rng, iters, deadline):
    """Anneal the dart set toward zero cost; return darts or None."""
    cur = _cost(a, N, D, T, darts)
    L = len(darts)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 1.5 * (1.0 - it / iters))
        new = list(darts)
        mv = rng.random()
        i, j = rng.sample(range(L), 2)
        if mv < 0.4:
            # swap B-endpoints of darts i and j (keeps B-degrees)
            ui, vi, gi = new[i]
            uj, vj, gj = new[j]
            new[i] = (ui, vj, gi)
            new[j] = (uj, vi, gj)
        elif mv < 0.7:
            # swap A-endpoints of darts i and j (keeps A-degrees)
            ui, vi, gi = new[i]
            uj, vj, gj = new[j]
            new[i] = (uj, vi, gi)
            new[j] = (ui, vj, gj)
        else:
            # re-randomize the group element of dart i
            ui, vi, _ = new[i]
            new[i] = (ui, vi, rng.randrange(N))
        if len(set(new)) != L:
            continue
        c = _cost(a, N, D, T, new)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            darts, cur = new, c
    return darts if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Random restarts over groups of order N until a zero-cost dart set is found."""
    groups = _groups(N)
    if not groups:
        return None
    while time.monotonic() < deadline:
        m, k, r = rng.choice(groups)
        T = _table(N, m, k, r)
        darts = _init_darts(a, d, N, rng)
        if darts is None:
            continue
        res = _sa(a, N, D, T, darts, rng, ITERS, deadline)
        if res is not None:
            return T, res
    return None


def _to_graph(a, N, T, darts):
    """Expand the dart set into an explicit (n, edges) graph."""
    edges = []
    for u, v, g in darts:
        for x in range(N):
            edges.append((u * N + x, (a + v) * N + T[x][g]))
    return 2 * a * N, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    usable = start + min(0.8 * time_limit, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact record-matching case: projective plane incidence graph.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 1:
        consider(2, [(0, 1)])
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < usable:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    arms = [2, 3, 1]
    st = {}
    for a in arms:
        st[a] = {
            'N': max(d + 1, best_n // (2 * a) + 1),
            'Nmax': moore // (2 * a),
            'budget': 2.0,
        }
    active = [a for a in arms if st[a]['N'] <= st[a]['Nmax']]

    while active and time.monotonic() < usable:
        for a in list(active):
            now = time.monotonic()
            if now >= usable:
                break
            s = st[a]
            N = max(s['N'], best_n // (2 * a) + 1)
            if N > s['Nmax']:
                active.remove(a)
                continue
            s['N'] = N
            att_deadline = min(usable, now + s['budget'])
            res = _attempt(a, N, d, D, rng, att_deadline)
            if res is None:
                s['budget'] = min(s['budget'] * 1.5, 8.0)
                continue
            T, darts = res
            n, e = _to_graph(a, N, T, darts)
            consider(n, e)
            s['N'] = N + max(1, N // 40)
            s['budget'] = 2.0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
