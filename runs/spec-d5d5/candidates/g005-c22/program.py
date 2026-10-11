import itertools
import math
import random
import time
from array import array

import lib

MAX_GROUPS_PER_N = 8     # semidirect groups kept in the search pool for each order N
WINDOW = 12              # candidate orders N in [top - WINDOW + 1, top]
CHUNK = 150              # annealing steps per scheduling slice
TIME_FRACTION = 0.85     # fraction of time_limit used before returning


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter. Identity is WLOG in S.
#
# Search strategy: a persistent pool of (order N, group, connection set) states.
# Each scheduling slice continues annealing the most promising state (lowest
# cost, with a penalty for states that already got many slices), so effort
# accumulates on promising groups instead of restarting from scratch.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
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


def _anneal_chunk(N, T, invs, d, D, rng, S, cur, iters, deadline, temp):
    """Continue simulated annealing over S = {0, s_1, ..., s_{d-1}} for a fixed number of steps."""
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S, cur


def _build_pool(cands, d, D, rng, deadline):
    """Create one annealing state per (order, group) for the candidate orders."""
    pool = []
    for N in sorted(cands, reverse=True):
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k, r in groups[:MAX_GROUPS_PER_N]:
            if time.monotonic() > deadline:
                return pool
            _, mul, inv = lib.semidirect_group(m, k, r)
            T = [array('i', (mul(x, g) for g in range(N))) for x in range(N)]
            invs = [inv(g) for g in range(N)]
            S = [0] + rng.sample(range(1, N), d - 1)
            cur = _unreached(N, T, invs, S, D)
            pool.append({'N': N, 'T': T, 'invs': invs, 'S': S,
                         'cost': cur, 'chunks': 0})
            if cur == 0:
                return pool
    return pool


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + TIME_FRACTION * time_limit - 1.0
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

    if D >= 2 and d >= 1:
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

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 3)
    lo = max(d + 1, best_n // 2 + 1, top - WINDOW + 1)
    cands = set(range(lo, top + 1))
    if not cands:
        return best

    pool = _build_pool(cands, d, D, rng, deadline)

    while pool and time.monotonic() < deadline:
        e = min(pool, key=lambda p: (p['cost'] + 0.3 * p['chunks'], rng.random()))
        temp = max(0.15, 1.0 * (0.97 ** e['chunks']))
        S, cur = _anneal_chunk(e['N'], e['T'], e['invs'], d, D, rng,
                               e['S'], e['cost'], CHUNK, deadline, temp)
        e['S'], e['cost'] = S, cur
        e['chunks'] += 1
        if cur == 0:
            N, T = e['N'], e['T']
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            # Only larger orders can improve now.
            pool = [p for p in pool if p['N'] > N]

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
