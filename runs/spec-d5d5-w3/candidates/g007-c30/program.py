import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------

MAX_GROUPS = 12        # groups tried per order N
N_WINDOW = 8           # bi-Cayley orders tried in a window just above the best
GREEDY_CANDS = 120     # candidates sampled per greedy extension step
SWAP_SAMPLES = 60      # (position, candidate) swaps sampled per tabu step
TABU_ITERS = 900       # improvement steps per restart
KICK_PROB = 0.04       # probability of accepting a worsening swap (diversification)
RESTARTS = 3           # restarts per (group, N)
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Baseline constructions (fallbacks; the parent's families).
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
# Bi-Cayley lifts over Z_m x|_r Z_k. Vertices A_x, B_y for x, y in G;
# A_x ~ B_{x g} for g in S, |S| = d, identity WLOG in S.
# Left translation is an automorphism, so eccentricities from A_0 and B_0 decide
# the diameter.
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
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k; T[x][g] = x*g, invs[g] = g^-1."""
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


def _greedy_tabu(N, T, invs, d, D, rng, deadline):
    """Build S greedily (add the element that most reduces unreached pairs), then
    improve by sampled swaps with occasional kicks. Returns S if valid, else None."""
    S = [0]
    while len(S) < d:
        if time.monotonic() > deadline:
            return None
        pool = [c for c in range(1, N) if c not in S]
        if len(pool) > GREEDY_CANDS:
            pool = rng.sample(pool, GREEDY_CANDS)
        best_c, best_v = None, None
        for c in pool:
            v = _unreached(N, T, invs, S + [c], D)
            if best_v is None or v < best_v:
                best_c, best_v = c, v
        S.append(best_c)

    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S[:], cur
    for _ in range(TABU_ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        cand_pick = None
        cand_val = None
        for _s in range(SWAP_SAMPLES):
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in S:
                continue
            S2 = S[:]
            S2[i] = c
            v = _unreached(N, T, invs, S2, D)
            if cand_val is None or v < cand_val:
                cand_val, cand_pick = v, S2
        if cand_pick is None:
            continue
        if cand_val <= cur or rng.random() < KICK_PROB:
            S, cur = cand_pick, cand_val
            if cur < best_v:
                best_S, best_v = S[:], cur
    return best_S if best_v == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                break
            S = _greedy_tabu(N, T, invs, d, D, rng, deadline)
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

    # Main search: greedy-tabu bi-Cayley lifts, beating the current best order.
    while best_n < moore and time.monotonic() < deadline:
        lo = best_n // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)
        if N <= d:
            continue
        res = _search_bicayley(d, D, N, rng, deadline)
        if res is not None:
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
