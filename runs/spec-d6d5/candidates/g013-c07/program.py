import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective plane PG(2,q) and generalized quadrangle W(q).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Haar graphs over non-abelian groups G = Z_m x| Z_k.
#
# Vertices a_x and b_y (x, y in G). Connection set S (|S| = d, distinct elements):
# a_x ~ b_{x*s} for s in S. Bipartite and d-regular. Left translation by h is an
# automorphism, so diameter <= D iff both a_e and b_e reach everything within D.
# This is a different family from the bi-Cayley voltage lifts: one orbit of
# group elements, a single connection set, and no per-layer B-assignments.
# ----------------------------------------------------------------------------

def _semidirect_candidates(G, rng, cap=30):
    """Non-abelian semidirect products Z_m x| Z_k of order G (plus cyclic as a last resort)."""
    cands = []
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    cands = cands[:cap]
    cands.append((G, 1, 1))  # cyclic fallback
    return cands


def _bfs_bad(G, D, Ps, Is, src):
    """Number of vertices NOT within distance D of src in the Haar graph."""
    n = 2 * G
    seen = bytearray(n)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                for p in Ps:
                    v = G + p[u]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                y = u - G
                for ip in Is:
                    v = ip[y]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return n - cnt


def _haar_search(G, d, D, mul, rng, deadline, iters):
    """Anneal a connection set S (|S| = d) so the Haar graph of this group has diameter <= D."""
    if d > G:
        return None
    cache = {}

    def perms(s):
        if s not in cache:
            p = [mul(x, s) for x in range(G)]
            ip = [0] * G
            for x, y in enumerate(p):
                ip[y] = x
            cache[s] = (p, ip)
        return cache[s]

    def cost(S):
        P = [perms(s) for s in S]
        Ps = [p for p, _ in P]
        Is = [ip for _, ip in P]
        return _bfs_bad(G, D, Ps, Is, 0) + _bfs_bad(G, D, Ps, Is, G)

    S = rng.sample(range(G), d)
    c = cost(S)
    T = 1.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        t = rng.randrange(G)
        if t in S:
            continue
        i = rng.randrange(d)
        S2 = S[:]
        S2[i] = t
        c2 = cost(S2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.1, T * 0.998)
    return S if c == 0 else None


def _haar_edges(G, S, mul):
    E = []
    for s in S:
        for x in range(G):
            E.append((x, G + mul(x, s)))
    return 2 * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: Haar graphs over non-abelian groups, climbing in group order.
    G = max(d, best_n // 2 + 1)
    fails = 0
    slice_len = max(1.5, 0.08 * time_limit)
    while time.monotonic() < deadline and fails < 6:
        cands = _semidirect_candidates(G, rng)
        found = False
        slice_deadline = min(deadline, time.monotonic() + slice_len)
        for (m, k, r) in cands[:2]:
            if time.monotonic() >= slice_deadline:
                break
            try:
                order, mul, _ = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            if order != G:
                continue
            S = _haar_search(G, d, D, mul, rng, slice_deadline, 2000)
            if S is not None:
                n, e = _haar_edges(G, S, mul)
                consider(n, e)
                found = True
                break
        if found:
            fails = 0
            G += max(1, G // 30)
        else:
            fails += 1
            G += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
