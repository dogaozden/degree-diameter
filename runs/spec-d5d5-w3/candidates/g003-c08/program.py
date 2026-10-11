import itertools
import math
import random
import time

import lib

ITERS = 400          # annealing steps per attempt
MAX_B = 4            # base-graph sides: b A-vertices and b B-vertices
K_CANDS = 8          # candidate totals tried per pass
MIN_BUDGET = 0.5     # seconds per candidate in the first pass


# ----------------------------------------------------------------------------
# Baseline families (cheap, always checked with lib.is_valid).
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
# Voltage lifts over semidirect products Z_m x| Z_k with a base of b A-vertices
# and b B-vertices. Each base dart (i, j, g) gives edges (A_i, x) -- (B_j, x*g)
# for all x in G. The base is d-regular: each A_i and each B_j has exactly d darts.
# Left multiplication by G is an automorphism, so the sources A_i,e and B_j,e
# (2b of them) decide the diameter.
# ----------------------------------------------------------------------------

def _groups(M):
    """Semidirect parameters (m, k, r) with m*k = M, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, M + 1):
        if M % k:
            continue
        m = M // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


_TCACHE = {}


def _table(m, k, r):
    """Return (order, T) with T[x][g] = x*g in the semidirect product."""
    key = (m, k, r)
    if key not in _TCACHE:
        if len(_TCACHE) > 40:
            _TCACHE.clear()
        order, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        _TCACHE[key] = (order, T)
    return _TCACHE[key]


def _structure(b, d, rng):
    """Base darts: d random permutations of range(b). Each A_i and B_j gets exactly d darts."""
    pairs = []
    for _ in range(d):
        perm = list(range(b))
        rng.shuffle(perm)
        for i in range(b):
            pairs.append((i, perm[i]))
    classes = {}
    for t, key in enumerate(pairs):
        classes.setdefault(key, []).append(t)
    cls_of = [classes[pairs[t]] for t in range(len(pairs))]
    return pairs, list(classes.values()), cls_of


def _cost(b, M, T, pairs, gs, D):
    """Total number of (source, vertex) pairs at distance > D over the 2b sources."""
    N = 2 * b * M
    off = b * M
    adj = [[] for _ in range(N)]
    for (i, j), g in zip(pairs, gs):
        ba = i * M
        bb = off + j * M
        for x in range(M):
            a = ba + x
            c = bb + T[x][g]
            adj[a].append(c)
            adj[c].append(a)
    total = 0
    sources = [i * M for i in range(b)] + [off + j * M for j in range(b)]
    for src in sources:
        seen = bytearray(N)
        seen[src] = 1
        count = 1
        frontier = [src]
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
        total += N - count
    return total


def _anneal(b, M, T, pairs, classes, cls_of, D, rng, iters, deadline):
    """Anneal the dart group elements to zero unreached pairs. Parallel darts get distinct elements."""
    gs = [0] * len(pairs)
    for idxs in classes:
        pool = rng.sample(range(M), len(idxs))
        for t, v in zip(idxs, pool):
            gs[t] = v
    cur = _cost(b, M, T, pairs, gs, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        t = rng.randrange(len(pairs))
        newg = rng.randrange(M)
        if newg == gs[t]:
            continue
        if any(gs[s] == newg for s in cls_of[t] if s != t):
            continue
        old = gs[t]
        gs[t] = newg
        v = _cost(b, M, T, pairs, gs, D)
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[t] = old
    return gs if cur == 0 else None


def _edges(b, M, T, pairs, gs):
    """Edge list of the lift; vertices A_i,x -> i*M+x and B_j,x -> b*M+j*M+x."""
    off = b * M
    out = []
    for (i, j), g in zip(pairs, gs):
        for x in range(M):
            out.append((i * M + x, off + j * M + T[x][g]))
    return 2 * b * M, out


def _attempt_total(options, d, D, rng, budget, consider):
    """Random (base, group, structure, annealing) attempts for one total order until budget ends."""
    end = time.monotonic() + budget
    while time.monotonic() < end:
        b, M = rng.choice(options)
        m, k, r = rng.choice(_groups(M))
        _, T = _table(m, k, r)
        pairs, classes, cls_of = _structure(b, d, rng)
        gs = _anneal(b, M, T, pairs, classes, cls_of, D, rng, ITERS, end)
        if gs is not None:
            n, e = _edges(b, M, T, pairs, gs)
            if consider(n, e):
                return True
    return False


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
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
            return True
        return False

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Cheap safe baselines.
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

    # Search over voltage lifts with base sizes b = 1..MAX_B.
    moore = lib._moore_bound(d, D)
    opts = {}
    for b in range(1, MAX_B + 1):
        for M in range(d, moore // (2 * b) + 1):
            tot = 2 * b * M
            if tot > moore:
                break
            opts.setdefault(tot, []).append((b, M))

    base_budget = max(MIN_BUDGET, 0.02 * time_limit)
    budget = base_budget
    while time.monotonic() < deadline:
        cands = sorted(t for t in opts if t > best_n)[:K_CANDS]
        if not cands:
            break
        improved = False
        for tot in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            bud = min(budget, deadline - now)
            if bud <= 0:
                break
            if _attempt_total(opts[tot], d, D, rng, bud, consider):
                improved = True
                break
        if not improved:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
