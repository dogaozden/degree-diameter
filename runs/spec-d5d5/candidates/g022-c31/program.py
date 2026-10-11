import math
import random
import time

import lib

ITERS = 500            # annealing steps per (group, voltage assignment) try
MAX_GROUPS = 40        # groups tried per attempt
MAX_CANDS = 30         # candidate (base size, order) pairs kept per search pass
PAIR_SIZES = (2, 3, 1) # base-graph sizes a per side: vertices = 2*a*N

_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    import itertools
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect products Z_m x| Z_k with a base graph of
# a vertices per side (a = 1 is a bi-Cayley graph; a = 2, 3 are new here).
#
# Vertices: A_{i,x} and B_{j,y}, indexed as i*N + x and (a+j)*N + y.
# A dart (i, j, g) joins A_{i,x} to B_{j, x*g} for all x in G.
# Row and column sums of the dart multiset equal d, so the lift is d-regular.
# Left multiplication is an automorphism, so BFS from one vertex per class
# decides the diameter.
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


def _table(N, key):
    """Multiplication table T[x][g] and inverses for the group keyed by (m, k, r)."""
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    if len(_TABLE_CACHE) > 200:
        _TABLE_CACHE.clear()
    m, k, r = key
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    _TABLE_CACHE[key] = (T, invs)
    return T, invs


def _adjacency(N, a, T, invs, darts):
    """Adjacency lists of the lift described by darts [(i, j, g), ...]."""
    off = a * N
    byA = [[] for _ in range(a)]
    byB = [[] for _ in range(a)]
    for i, j, g in darts:
        byA[i].append((j, g))
        byB[j].append((i, invs[g]))
    adj = [None] * (2 * a * N)
    for i in range(a):
        lst = byA[i]
        base = i * N
        for x in range(N):
            row = T[x]
            adj[base + x] = [off + j * N + row[g] for j, g in lst]
    for j in range(a):
        lst = byB[j]
        base = off + j * N
        for y in range(N):
            row = T[y]
            adj[base + y] = [i * N + row[h] for i, h in lst]
    return adj


def _unreached(N, a, adj, D):
    """Ordered (source, vertex) pairs at distance > D, over one source per vertex class."""
    V = len(adj)
    total = 0
    for src in range(0, V, N):  # class starts: 2a sources
        seen = bytearray(V)
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
        total += V - count
    return total


def _random_darts(a, d, N, rng):
    """Dart multiset with row and column sums d: a sum of d random permutations, distinct voltages per (i, j)."""
    darts = []
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for i in range(a):
            darts.append([i, p[i], 0])
    groups = {}
    for t in darts:
        groups.setdefault((t[0], t[1]), []).append(t)
    for lst in groups.values():
        for t, v in zip(lst, rng.sample(range(N), len(lst))):
            t[2] = v
    return darts


def _anneal(N, a, d, D, T, invs, rng, deadline):
    """Anneal voltages to zero unreached pairs; return darts on success, else None."""
    darts = _random_darts(a, d, N, rng)
    adj = _adjacency(N, a, T, invs, darts)
    cur = _unreached(N, a, adj, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        t = rng.randrange(len(darts))
        i, j, g_old = darts[t]
        used = set()
        for s_idx, s in enumerate(darts):
            if s_idx != t and s[0] == i and s[1] == j:
                used.add(s[2])
        choices = [g for g in range(N) if g not in used and g != g_old]
        if not choices:
            continue
        darts[t][2] = rng.choice(choices)
        adj2 = _adjacency(N, a, T, invs, darts)
        v = _unreached(N, a, adj2, D)
        temp = max(0.3, 2.0 * (1.0 - it / ITERS))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            adj = adj2
        else:
            darts[t][2] = g_old
    return darts if cur == 0 else None


def _attempt(N, a, d, D, rng, deadline):
    """Try groups of order N for a base of size a; return (T, darts) on success or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for key in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _table(N, key)
        darts = _anneal(N, a, d, D, T, invs, rng, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift_edges(N, a, T, darts):
    """Return (vertex count, edge list) for the lift."""
    off = a * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, off + j * N + T[x][g]))
    return 2 * a * N, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, time_limit - 5.0)
    deadline = start + max(0.0, budget)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best_n = 1
    best_e = []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n = n
            best_e = e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best_n, best_e

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

    # Lift search: candidate (total vertices, a, N) pairs above the current best.
    if d >= 2 and D >= 2 and time.monotonic() < deadline:
        Moore = lib._moore_bound(d, D)
        pairs = []
        for a in PAIR_SIZES:
            lo = max(d, best_n // (2 * a) + 1)
            hi = Moore // (2 * a)
            for N in range(lo, hi + 1):
                pairs.append((2 * a * N, a, N))
        pairs.sort()
        if len(pairs) > MAX_CANDS:
            idx = sorted({round(k * (len(pairs) - 1) / (MAX_CANDS - 1))
                          for k in range(MAX_CANDS)})
            pairs = [pairs[i] for i in idx]
        cands = pairs

        while cands and time.monotonic() < deadline:
            progressed = False
            for idx in range(len(cands)):
                total, a, N = cands[idx]
                if total <= best_n:
                    continue
                now = time.monotonic()
                if now >= deadline:
                    break
                att = max(0.3, (deadline - now) / (2 * (len(cands) - idx)))
                res = _attempt(N, a, d, D, rng, min(deadline, now + att))
                if res is None:
                    continue
                n, e = _lift_edges(N, a, res[0], res[1])
                consider(n, e)
                cands = [c for c in cands if c[0] > total]
                progressed = True
                break
            if not progressed and time.monotonic() >= deadline:
                break

    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []
    return best_n, best_e
