import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe structured families (fallbacks).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: bipartite Haar graphs over finite-ish groups.
#
# For a group G (semidirect product Z_m x| Z_k, order G) and a connection set
# S of size d, H(G,S) has vertices a_g, b_h (g,h in G) with a_g ~ b_{gs}.
# Left multiplication is an automorphism, so the graph has diameter <= D iff a
# BFS of depth D from a_identity and from b_identity reaches everything.
#
# Search: simulated annealing over the set S, minimising the number of
# unreached (source, vertex) pairs. Groups of order G are tried for G just above
# the current best half-order, so each success strictly improves the graph.
# ----------------------------------------------------------------------------

def _group_candidates(G):
    """All (m, k, r) with m * k = G giving a semidirect product Z_m x| Z_k."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _anneal(d, D, G, mulf, invf, rng, slice_end):
    """Anneal a connection set S (|S| = d) in group G so H(G,S) has diameter <= D.

    Returns (n, edges) on success, otherwise None.
    """
    if G < d:
        return None
    fwd_cache = {}
    bwd_cache = {}

    def perms(s):
        if s not in fwd_cache:
            fwd_cache[s] = [mulf(g, s) for g in range(G)]
            si = invf(s)
            bwd_cache[s] = [mulf(h, si) for h in range(G)]
        return fwd_cache[s], bwd_cache[s]

    def cost(S):
        fl = []
        bl = []
        for s in S:
            f, b = perms(s)
            fl.append(f)
            bl.append(b)
        total = 0
        for src in (0, G):
            seen = bytearray(2 * G)
            seen[src] = 1
            frontier = [src]
            count = 1
            for _ in range(D):
                nxt = []
                for u in frontier:
                    if u < G:
                        for p in fl:
                            v = G + p[u]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                    else:
                        h = u - G
                        for p in bl:
                            v = p[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                count += len(nxt)
                frontier = nxt
                if not frontier:
                    break
            total += 2 * G - count
        return total

    S = rng.sample(range(G), d)
    cur = cost(S)
    best = cur
    best_S = list(S)
    t0 = time.monotonic()
    span = max(slice_end - t0, 1e-3)
    while cur > 0 and time.monotonic() < slice_end:
        frac = (time.monotonic() - t0) / span
        T = 2.0 * (1.0 - frac) + 0.05
        i = rng.randrange(d)
        s_old = S[i]
        s_new = rng.randrange(G)
        if s_new in S:
            continue
        S[i] = s_new
        c2 = cost(S)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
            if cur < best:
                best = cur
                best_S = list(S)
        else:
            S[i] = s_old

    if best != 0:
        return None
    E = []
    for s in best_S:
        f, _ = perms(s)
        for g in range(G):
            E.append((g, G + f[g]))
    return 2 * G, E


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    budget = max(0.5 * time_limit, min(0.8 * time_limit, time_limit - 5.0))
    deadline = t_start + budget
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib._moore_bound(d, D)

    if best_n < moore:
        if D >= 3:
            try:
                pg = _best_pg(d)
                if pg is not None:
                    consider(pg[0], pg[1])
            except Exception:
                pass

        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except Exception:
                pass

        if D >= 4 and time.monotonic() < deadline:
            try:
                gq = _best_gq(d)
                if gq is not None:
                    consider(gq[0], gq[1])
            except Exception:
                pass

    # Main search: Haar graphs over semidirect products, targeting orders just
    # above the current best half-order.
    if d >= 3 and D >= 2 and best_n < moore:
        G = best_n // 2 + 1
        slice_len = max(1.0, budget * 0.1)
        while time.monotonic() < deadline and 2 * G <= moore:
            cands = _group_candidates(G)
            if not cands:
                G += 1
                continue
            rng.shuffle(cands)
            found = None
            for (m, k, r) in cands:
                if time.monotonic() >= deadline:
                    break
                try:
                    order, mulf, invf = lib.semidirect_group(m, k, r)
                except ValueError:
                    continue
                slice_end = min(deadline, time.monotonic() + slice_len)
                try:
                    res = _anneal(d, D, order, mulf, invf, rng, slice_end)
                except Exception:
                    res = None
                if res is not None:
                    found = res
                    break
            if found is not None:
                consider(found[0], found[1])
                G = max(G + 1, best_n // 2 + 1)
            # On failure we retry the same order with fresh groups and seeds.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
