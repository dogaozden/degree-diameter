import itertools
import math
import random
import time

import lib

ITERS = 1500          # annealing steps per (group, pattern, N) try
T_HOT = 2.0           # initial annealing temperature (unreached-pair units)
T_COLD = 0.2          # final annealing temperature
GROUPS_PER_TRY = 8    # groups tried per attempt
MAX_BUDGET = 16.0     # cap on per-order time budget (seconds)


# ----------------------------------------------------------------------------
# Baseline families (always validated before use).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Generalized bi-Cayley lifts with a_ parts on each side.
#
# Vertices A_{i,x} and B_{j,y} for i, j in range(a), x, y in G (|G| = N).
# A pattern pat (sum = d) gives cell counts c_ij = pat[(j - i) % a], so every
# vertex has degree d. Each cell (i, j) carries a set of c_ij distinct voltages
# S_ij, with edges A_{i,x} -- B_{j, x*s} for s in S_ij. Left multiplication by G
# is an automorphism, so BFS from A_{i,e} and B_{j,e} decides the diameter.
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


def _compositions(total, parts):
    """All tuples of `parts` nonnegative ints summing to `total`."""
    if parts == 1:
        yield (total,)
        return
    for x in range(total + 1):
        for rest in _compositions(total - x, parts - 1):
            yield (x,) + rest


def _cells(a, pat):
    """List of (i, j, count) for the circulant cell pattern with count > 0."""
    return [(i, j, pat[(j - i) % a]) for i in range(a) for j in range(a)
            if pat[(j - i) % a] > 0]


def _adj(N, a, cells, vol, T):
    """Adjacency lists of the lift; A-parts are 0..a*N-1, B-parts follow."""
    n = 2 * a * N
    base_b = a * N
    adj = [[] for _ in range(n)]
    for (i, j, _), S in zip(cells, vol):
        off_b = base_b + j * N
        for x in range(N):
            row = T[x]
            u = i * N + x
            for s in S:
                v = off_b + row[s]
                adj[u].append(v)
                adj[v].append(u)
    return adj


def _cost(n, D, adj, srcs):
    """Total number of (source, vertex) pairs not within distance D."""
    total = 0
    for src in srcs:
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _anneal(N, a, cells, T, D, rng, iters, deadline):
    """Anneal voltage sets so that every source reaches everything within D."""
    n = 2 * a * N
    srcs = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    vol = [rng.sample(range(N), c) for _, _, c in cells]
    cur = _cost(n, D, _adj(N, a, cells, vol, T), srcs)
    if cur == 0:
        return vol
    for it in range(iters):
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        k = rng.randrange(len(cells))
        p = rng.randrange(len(vol[k]))
        g = rng.randrange(N)
        if g in vol[k]:
            continue
        old = vol[k][p]
        vol[k][p] = g
        v = _cost(n, D, _adj(N, a, cells, vol, T), srcs)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            if cur == 0:
                return vol
        else:
            vol[k][p] = old
    return None


def _attempt(a, pat, N, d, D, rng, deadline):
    """Try several groups of order N for one pattern; return (T, cells, vol) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    cells = _cells(a, pat)
    for m, k, r in groups[:GROUPS_PER_TRY]:
        if time.monotonic() > deadline:
            return None
        order, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        vol = _anneal(N, a, cells, T, D, rng, ITERS, deadline)
        if vol is not None:
            return T, cells, vol
    return None


def _edges_from(N, a, T, cells, vol):
    edges = []
    base_b = a * N
    for (i, j, _), S in zip(cells, vol):
        for x in range(N):
            row = T[x]
            for s in S:
                edges.append((i * N + x, base_b + j * N + row[s]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
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

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    # Lift families with a parts per side. Larger a gives more base structure.
    a_values = [2, 3, 4, 1]
    pats = {a: list(_compositions(d, a)) for a in a_values}
    Nt = {a: max(d, best_n // (2 * a) + 1) for a in a_values}
    budget = {a: 1.0 for a in a_values}

    while time.monotonic() < deadline:
        progressed = False
        for a in a_values:
            if time.monotonic() >= deadline:
                break
            Nt[a] = max(Nt[a], max(d, best_n // (2 * a) + 1))
            N = Nt[a]
            if 2 * a * N > moore:
                continue
            pat = rng.choice(pats[a])
            now = time.monotonic()
            att_deadline = min(deadline, now + budget[a])
            res = _attempt(a, pat, N, d, D, rng, att_deadline)
            progressed = True
            if res is None:
                budget[a] = min(budget[a] * 2, MAX_BUDGET)
                continue
            T, cells, vol = res
            edges = _edges_from(N, a, T, cells, vol)
            consider(2 * a * N, edges)
            Nt[a] = N + 1
            budget[a] = 1.0
        if not progressed:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
