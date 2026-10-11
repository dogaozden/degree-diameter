import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

SLICE = 3.0            # seconds of annealing per sampled group
ANNEAL_ITERS = 2000    # annealing steps per sampled group
WINDOW = 40            # sample group orders this far above the current lower bound first
_CACHE = {}
_CACHE_CAP = 8         # group tables are N x N, keep only a few


# ----------------------------------------------------------------------------
# Permutation-group atoms (non-metacyclic groups the semidirect family misses).
# name -> (generators on a small point set, expected order)
# ----------------------------------------------------------------------------

PERM_GENS = {
    "S3": ([(1, 2, 0), (1, 0, 2)], 6),
    "A4": ([(1, 2, 0, 3), (1, 0, 3, 2)], 12),
    "S4": ([(1, 2, 3, 0), (1, 0, 2, 3)], 24),
    "A5": ([(1, 2, 0, 3, 4), (0, 1, 3, 4, 2)], 60),
    "S5": ([(1, 2, 3, 4, 0), (1, 0, 2, 3, 4)], 120),
    # PSL(2,7) acting on the projective line over F_7 (point 7 = infinity).
    "PSL27": ([[1, 2, 3, 4, 5, 6, 0, 7],
               [0, 4, 1, 5, 2, 6, 3, 7],
               [7, 6, 3, 2, 5, 4, 1, 0]], 168),
}


# ----------------------------------------------------------------------------
# D = 3 baseline: projective plane incidence graph when d - 1 is a prime power.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group construction. A group is (N, T, I): T[x][y] = x*y, I[x] = x^-1,
# identity is element 0.
# ----------------------------------------------------------------------------

def _semidirect_params(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _from_mul(order, mul, inv):
    T = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return order, T, I


def _group_from_perms(gens, cap):
    """Closure of permutation generators; returns (N, T, I) or None if the order exceeds cap."""
    n = len(gens[0])
    ident = tuple(range(n))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple(p[i] for i in g)
                if q not in index:
                    if len(elems) >= cap:
                        return None
                    index[q] = len(elems)
                    elems.append(q)
                    nxt.append(q)
        frontier = nxt
    N = len(elems)
    T = [[index[tuple(elems[x][j] for j in elems[y])] for y in range(N)] for x in range(N)]
    I = [row.index(0) for row in T]
    return N, T, I


def _product(G1, G2):
    N1, T1, I1 = G1
    N2, T2, I2 = G2
    N = N1 * N2
    T = []
    for x in range(N):
        a1, a2 = divmod(x, N2)
        r1 = T1[a1]
        r2 = T2[a2]
        T.append([r1[b1] * N2 + r2[b2] for b1 in range(N1) for b2 in range(N2)])
    I = [I1[x // N2] * N2 + I2[x % N2] for x in range(N)]
    return N, T, I


def _order(spec):
    kind = spec[0]
    if kind == "cyc":
        return spec[1]
    if kind == "sd":
        return spec[1] * spec[2]
    if kind == "perm":
        return PERM_GENS[spec[1]][1]
    return _order(spec[1]) * _order(spec[2])


def _build(spec):
    if spec in _CACHE:
        return _CACHE[spec]
    kind = spec[0]
    if kind == "cyc":
        k = spec[1]
        res = (k, [[(x + y) % k for y in range(k)] for x in range(k)],
               [(-x) % k for x in range(k)])
    elif kind == "sd":
        res = _from_mul(*lib.semidirect_group(spec[1], spec[2], spec[3]))
    elif kind == "perm":
        res = _group_from_perms(PERM_GENS[spec[1]][0], 400)
    else:
        g1 = _build(spec[1])
        g2 = _build(spec[2])
        res = None if (g1 is None or g2 is None) else _product(g1, g2)
    if len(_CACHE) >= _CACHE_CAP:
        _CACHE.clear()
    _CACHE[spec] = res
    return res


def _all_specs(hi):
    """All candidate group specs with order <= hi, as (order, spec) pairs."""
    sd = []
    for N in range(2, hi + 1):
        for m, k, r in _semidirect_params(N):
            sd.append(("sd", m, k, r))
    out = list(sd)
    atoms = [("perm", name) for name in PERM_GENS] + [("cyc", k) for k in range(2, 31)]
    for i, a in enumerate(atoms):
        for b in atoms[i:]:
            if a[0] == "cyc" and b[0] == "cyc":
                continue
            if _order(a) * _order(b) <= hi:
                out.append(("prod", a, b))
    for k in (2, 3, 4):
        for s in sd:
            if k * _order(s) <= hi:
                out.append(("prod", ("cyc", k), s))
    return [(_order(s), s) for s in out]


# ----------------------------------------------------------------------------
# Bi-Cayley lift: vertices A_x = x and B_y = N + y; edge A_x -- B_{x s}, s in S.
# Identity is WLOG in S. Diameter is decided by the distances from A_0 and B_0.
# ----------------------------------------------------------------------------

def _unreached(N, T, I, S, D):
    Sinv = [I[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        count = 1
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


def _anneal(N, T, I, d, D, rng, deadline, iters):
    if N < d:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, I, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 7) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, I, S2, D)
        temp = 0.3 + 1.5 * (1.0 - it / iters)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Search loop: sample groups, anneal connection sets, keep improvements.
# ----------------------------------------------------------------------------

def _search(d, D, moore, deadline, rng, best_n, consider):
    hi = moore // 2
    specs = _all_specs(hi)
    while time.monotonic() < deadline:
        lo = best_n() // 2 + 1
        if lo > hi:
            break
        pool = [s for o, s in specs if lo <= o <= min(hi, lo + WINDOW)]
        if not pool:
            pool = [s for o, s in specs if lo <= o <= hi]
        if not pool:
            break
        grp = _build(rng.choice(pool))
        if grp is None:
            continue
        N, T, I = grp
        if N < d + 1:
            continue
        slice_dl = min(deadline, time.monotonic() + SLICE)
        S = _anneal(N, T, I, d, D, rng, slice_dl, ANNEAL_ITERS)
        if S is not None:
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound for D = 2.
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

    if best[0] < moore:
        try:
            _search(d, D, moore, deadline, rng, lambda: best[0], consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
