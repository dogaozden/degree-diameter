import itertools
import math
import random
import time

import lib

TS = (1, 2, 3, 4)          # base sizes: t vertices per side, lifted by a group of order N
ITERS = 2500               # annealing steps per attempt
WINDOW_MIN = 12            # how far above the current best order to look
MAX_N_EVAL = 3000          # never search on graphs larger than this


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Generalised lift search.
#
# Base graph: t vertices A_0..A_{t-1} and t vertices B_0..B_{t-1}, with d
# perfect matchings sig[k] (permutations of range(t)) and voltages volt[k][i]
# in a group G of order N. Dart (k, i) joins A_i to B_{sig[k][i]} via the
# voltage. Lifted vertices are A_{i,x} = i*N + x and B_{j,y} = t*N + j*N + y,
# with the edge A_{i,x} -- B_{j, x*g}. The lift is d-regular (before merging
# duplicate edges), bipartite, and G acts by left multiplication on each fibre.
# So eccentricities only need to be checked from the t A-representatives and
# the t B-representatives.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) giving groups Z_m x|_r Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(N, m, k, r):
    """Multiplication table and inverse list for the group of order N."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    mulT = [[mul(x, g) for g in range(N)] for x in range(N)]
    invT = [inv(g) for g in range(N)]
    return mulT


def _bad(t, N, D, sig, volt, mulT):
    """Number of (source-class, vertex) pairs not within distance D."""
    n = 2 * t * N
    adj = [[] for _ in range(n)]
    off_b = t * N
    for kk in range(len(sig)):
        sk = sig[kk]
        vk = volt[kk]
        for i in range(t):
            j = sk[i]
            g = vk[i]
            ob = off_b + j * N
            ba = i * N
            for x in range(N):
                a = ba + x
                b = ob + mulT[x][g]
                adj[a].append(b)
                adj[b].append(a)
    bad = 0
    sources = [i * N for i in range(t)] + [off_b + j * N for j in range(t)]
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
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
        bad += n - cnt
    return bad


def _edges(t, N, sig, volt, mulT):
    """Deduplicated edge list of the lift."""
    es = set()
    off_b = t * N
    for kk in range(len(sig)):
        sk = sig[kk]
        vk = volt[kk]
        for i in range(t):
            j = sk[i]
            g = vk[i]
            ob = off_b + j * N
            for x in range(N):
                es.add((i * N + x, ob + mulT[x][g]))
    return sorted(es)


def _search(t, N, d, D, rng, deadline, iters):
    """Anneal voltages and matchings until every pair is within distance D, or give up."""
    groups = _groups(N)
    m, k, r = rng.choice(groups)
    mulT = _tables(N, m, k, r)
    sig = []
    for _ in range(d):
        p = list(range(t))
        rng.shuffle(p)
        sig.append(p)
    volt = [[rng.randrange(N) for _ in range(t)] for _ in range(d)]
    cur = _bad(t, N, D, sig, volt, mulT)
    T0 = 1.5
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.05, T0 * (1.0 - it / iters))
        kk = rng.randrange(d)
        if t == 1 or rng.random() < 0.7:
            i = rng.randrange(t)
            old = volt[kk][i]
            volt[kk][i] = rng.randrange(N)
            v = _bad(t, N, D, sig, volt, mulT)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volt[kk][i] = old
        else:
            i1, i2 = rng.sample(range(t), 2)
            sk = sig[kk]
            sk[i1], sk[i2] = sk[i2], sk[i1]
            v = _bad(t, N, D, sig, volt, mulT)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                sk[i1], sk[i2] = sk[i2], sk[i1]
    if cur != 0:
        return None
    return _edges(t, N, sig, volt, mulT)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
    budget = 0.3

    while time.monotonic() < deadline:
        window = max(WINDOW_MIN, best_n // 8)
        cands = set()
        for t in TS:
            lo = best_n // (2 * t) + 1
            hi = (best_n + window) // (2 * t)
            for N in range(max(lo, 1), max(hi, lo) + 1):
                n = 2 * t * N
                if n > moore or n > MAX_N_EVAL:
                    continue
                cands.add((n, t, N))
        if not cands:
            break
        cands = sorted(cands)

        success = False
        for n, t, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            att = min(deadline, now + budget)
            res = _search(t, N, d, D, rng, att, ITERS)
            if res is None:
                continue
            consider(n, res)
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
