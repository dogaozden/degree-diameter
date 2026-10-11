import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallback families: projective plane, Araujo-Pardo-Lopez, generalized quadrangle.
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
    """W(q) for the largest prime power q with q + 1 <= d (small q only)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family: Haar-type lifts over non-cyclic groups Z_m x| Z_k, k = 1 base orbit.
#
# Vertices: A_g = g and B_h = G + h, for g, h in the group of order G.
# Connection set S (size d, identity included WLOG since right-translating S
# by t is an isomorphism): A_g ~ B_{g*s} for s in S.
# Left multiplication is an automorphism, so only BFS from A_e and B_e is needed.
# ----------------------------------------------------------------------------

def _groups_of_order(G, rng, max_r=4):
    """Return a list of (m, k, r) with m*k = G and semidirect Z_m x| Z_k valid."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        rng.shuffle(rs)
        for r in rs[:max_r]:
            out.append((m, k, r))
    return out


def _cost_haar(G, perms, D):
    """Unreached (source, vertex) pairs within distance D from A_e and B_e. Zero means valid."""
    N = 2 * G
    adj = [[] for _ in range(N)]
    for p in perms:
        for g in range(G):
            a = g
            b = G + p[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in (0, G):
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
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _climb(G, mul, cache, d, D, rng, until):
    """Annealed hill-climb over connection sets S (identity included). Returns (S, perms) or None."""
    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    if G - 1 < d - 1:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    perms = [perm(s) for s in S]
    c = _cost_haar(G, perms, D)
    T = 2.0
    while c > 0 and time.monotonic() < until:
        i = rng.randrange(1, d)
        s_new = rng.randrange(1, G)
        if s_new in S:
            continue
        S2 = S[:]
        S2[i] = s_new
        p2 = perms[:]
        p2[i] = perm(s_new)
        c2 = _cost_haar(G, p2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, perms, c = S2, p2, c2
        T = max(0.3, T * 0.999)
    if c == 0:
        return S, perms
    return None


def _edges_haar(G, perms):
    E = []
    for p in perms:
        for g in range(G):
            E.append((g, G + p[g]))
    return 2 * G, E


def _group_search(d, D, target, rng, deadline, consider):
    """Round-robin hill-climb over Haar lifts for orders target, target+1, ... ."""
    tasks = []
    for G in [target] + list(range(target + 1, target + 60)):
        groups = _groups_of_order(G, rng)
        rng.shuffle(groups)
        for m, k, r in groups:
            order, mul, _ = lib.semidirect_group(m, k, r)
            tasks.append((order, mul, {}))
    if not tasks:
        return
    slice_t = 2.0
    while time.monotonic() < deadline:
        for G, mul, cache in tasks:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _climb(G, mul, cache, d, D, rng, min(deadline, now + slice_t))
            if res is not None:
                _, perms = res
                n, e = _edges_haar(G, perms)
                consider(n, e)
        slice_t = min(slice_t * 1.5, 8.0)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 6)
    if deadline <= start:
        deadline = start + 0.5 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

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

    if D >= 4 and d >= 3:
        target = 342 if (d, D) == (6, 5) else best_n // 2 + 1
        _group_search(d, D, target, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
