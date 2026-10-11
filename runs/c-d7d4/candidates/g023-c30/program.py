import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases: W(q) generalized quadrangle (D >= 4), PG(2, q) (D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Points and totally isotropic lines of W(q) as a bipartite incidence graph (degree q+1, order 2(q+1)(q^2+1))."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Generic helpers: balls, bipartition, cover growth, cross-edge saturation.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within D-1 of the cover; keeps diameter <= D."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(30):
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order (only shortens distances)."""
    out = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return out


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley graphs over small non-abelian groups.
#
# Let G be a finite group and S a set of d elements. The bipartite graph with
# vertices (g, 0), (g, 1) and edges (g, 0) ~ (g s, 1) for s in S is d-regular
# and bipartite, with 2|G| vertices. Left multiplication by G is an automorphism
# that acts regularly on each side, so the diameter check only needs BFS from
# (1, 0) and (1, 1). The search picks a group (cyclic or semidirect Z_m x| Z_k)
# and hill-climbs S to zero bad pairs. Each success gives a larger valid graph.
# ----------------------------------------------------------------------------

def _group_candidates(G):
    """(m, k, r) with G = m*k, giving Z_m x|_r Z_k (r = 1 is the direct product, k = 1 cyclic)."""
    out = []
    for m in range(2, G + 1):
        if G % m:
            continue
        k = G // m
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_tables(m, k, r):
    G, mul, inv = lib.semidirect_group(m, k, r)
    tbl = [[mul(x, y) for y in range(G)] for x in range(G)]
    invs = [inv(x) for x in range(G)]
    return G, tbl, invs


def _bad(G, nb0, nb1, D):
    """Unreached (source, target) pairs within distance D from (1,0) and (1,1)."""
    total = 0
    for side in (0, 1):
        src = side * G
        seen = bytearray(2 * G)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                nbrs = nb0[u] if u < G else nb1[u - G]
                for w in nbrs:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * G - count
    return total


def _cost_S(G, tbl, invs, S, D):
    nb0 = [[G + row[s] for s in S] for row in tbl]
    nb1 = [[row[invs[s]] for s in S] for row in tbl]
    return _bad(G, nb0, nb1, D)


def _search_group(G, tbl, invs, d, D, rng, deadline, iters):
    """Hill-climb a generating set S of size d. Returns S with zero bad pairs, or None."""
    S = rng.sample(range(G), d)
    cost = _cost_S(G, tbl, invs, S, D)
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = list(S)
        S2[i] = x
        c2 = _cost_S(G, tbl, invs, S2, D)
        if c2 <= cost or rng.random() < 0.02:
            S, cost = S2, c2
    return S if cost == 0 else None


def _bicayley_search(d, D, rng, deadline, best_fn, consider):
    """Repeatedly try bi-Cayley graphs with orders just above the current best."""
    hi = lib.moore_bound(d, D) // 2
    while time.monotonic() < deadline:
        lo = max(best_fn() // 2 + 1, d)
        if lo > hi:
            break
        G = lo + int((hi - lo) * rng.random() ** 2)
        cands = _group_candidates(G)
        if not cands:
            continue
        m, k, r = rng.choice(cands)
        G2, tbl, invs = _group_tables(m, k, r)
        attempt_end = min(deadline, time.monotonic() + 4.0)
        S = _search_group(G2, tbl, invs, d, D, rng, attempt_end, 4000)
        if S is None:
            continue
        edges = [(g, G2 + tbl[g][s]) for g in range(G2) for s in S]
        consider(2 * G2, edges)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    moore = lib.moore_bound(d, D)

    # Structured base plus cover growth (safe path, keeps the generalized quadrangle result).
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.30 * time_limit, rng)
            consider(n1, e1)

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= moore:
        return best_n, list(best_e)

    # Bold stage: bi-Cayley search over small groups.
    if D >= 2 and time.monotonic() < deadline:
        _bicayley_search(d, D, rng, deadline, lambda: best_n, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
