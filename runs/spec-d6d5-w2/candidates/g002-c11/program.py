import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families (safe, cheap): projective plane, Araujo-Pardo-Lopez,
# generalized quadrangle W(q), and Haar graphs for small D.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Bold new family for D >= 5: bi-Cayley graphs over a random (often non-cyclic)
# group G, with B-side connection set S of size d. Vertex A_g = g, B_h = G + h,
# and A_g ~ B_{g*s} for s in S. The graph is bipartite, d-regular, and
# left-translation invariant, so the diameter is decided by BFS from
# the identity on each side. Search S with tabu moves on single elements.
# ----------------------------------------------------------------------------

def _sample_group(G, rng, k2_choices):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice(k2_choices)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _unreached(adj, src, D, N):
    """Number of vertices not within distance D of src."""
    seen = bytearray(N)
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
    return N - count


def _tabu_bicay(d, D, G, mul, rng, deadline, iters, sample):
    """Tabu search over connection sets S of size d in a group of order G.

    Cost = unreached pairs from the identity on the A side and on the B side.
    Returns (best_cost, best_S).
    """
    N = 2 * G
    cache = {}

    def perm_of(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    def cost(S):
        adj = [[] for _ in range(N)]
        for s in S:
            p = perm_of(s)
            for g in range(G):
                h = G + p[g]
                adj[g].append(h)
                adj[h].append(g)
        return _unreached(adj, 0, D, N) + _unreached(adj, G, D, N)

    S = rng.sample(range(G), d)
    cur = cost(S)
    best_c, best_S = cur, list(S)
    tabu = {}
    for it in range(iters):
        if best_c == 0 or time.monotonic() > deadline:
            break
        inS = set(S)
        move, mc = None, None
        for _ in range(sample):
            i = rng.randrange(d)
            new = rng.randrange(G)
            if new in inS or tabu.get(new, -1) > it:
                continue
            T = S[:]
            T[i] = new
            c = cost(T)
            if mc is None or c < mc:
                mc, move = c, (i, new)
        if move is None:
            continue
        i, new = move
        old = S[i]
        S[i] = new
        cur = mc
        tabu[old] = it + 8 + rng.randrange(5)
        if cur < best_c:
            best_c, best_S = cur, list(S)
    return best_c, best_S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Cheap baseline families.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    big = D >= 5
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        # Small D: occasionally try Haar graphs.
        if not big and haar_miss < 4 and rng.random() < 0.4:
            m = haar_m
            haar_m += 1
            S = _search_haar(d, D, m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            continue

        # Bi-Cayley search: group order just above the current best half-order.
        base = best_n // 2
        lo = max(d + 1, base + 1)
        hi = lo + max(4, lo // 12)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng, k2_pool)
        if g is None:
            continue
        order, mul = g
        if order < d + 1:
            continue
        bc, bS = _tabu_bicay(d, D, order, mul, rng, deadline, 120, 16)
        if bc == 0:
            E = [(x, order + mul(x, s)) for s in bS for x in range(order)]
            consider(2 * order, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
