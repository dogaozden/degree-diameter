import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases.
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


# ----------------------------------------------------------------------------
# Twin augmentation: a twin of x has the same neighbourhood, so distances are
# preserved and the graph stays bipartite. Each neighbour takes at most its slack.
# ----------------------------------------------------------------------------

def _twin_augment(n, edges, d, rng, trials):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    best = []
    for _ in range(trials):
        slack = [d - len(a) for a in adj]
        order = list(range(n))
        rng.shuffle(order)
        chosen = []
        for x in order:
            if adj[x] and all(slack[w] > 0 for w in adj[x]):
                for w in adj[x]:
                    slack[w] -= 1
                chosen.append(x)
        if len(chosen) > len(best):
            best = chosen
    E = list(edges)
    N = n
    for x in best:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# Bold construction: bi-Cayley (Haar-type) graphs over semidirect products
# Z_m x| Z_k of order G. Left vertex i (0..G-1) is adjacent to right vertex
# G + i*s for s in S, so the graph is d-regular and bipartite of order 2G.
# Left multiplication is an automorphism, so only the two identity vertices
# need BFS checks: left-left, left-right from left id, right-right and
# right-left from right id.
# ----------------------------------------------------------------------------

def _group_tables(m, k, r):
    G, mul, inv = lib.semidirect_group(m, k, r)
    mt = [[mul(x, y) for y in range(G)] for x in range(G)]
    iv = [inv(x) for x in range(G)]
    return G, mt, iv


def _pick_group(G, rng):
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    k = rng.choice(divs)
    m = G // k
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    return m, k, r


def _haar_cost(G, mt, iv, S, D):
    """Number of (source, target) pairs at distance > D from the two identity vertices."""
    invS = [iv[s] for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(2 * G)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = mt[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = mt[u - G]
                    for si in invS:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * G - cnt
    return total


def _haar_search(d, D, G, mt, iv, rng, deadline, iters):
    if G < d:
        return None
    S = rng.sample(range(G), d)
    c = _haar_cost(G, mt, iv, S, D)
    best_c, best_S = c, S[:]
    it = 0
    while best_c > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _haar_cost(G, mt, iv, S, D)
        T = 2.0 * (0.2 ** (it / iters))
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
            if c < best_c:
                best_c, best_S = c, S[:]
        else:
            S[i] = old
    return best_S if best_c == 0 else None


def _haar_edges(G, mt, S):
    E = []
    for i in range(G):
        row = mt[i]
        for s in S:
            E.append((i, G + row[s]))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            tn, te = _twin_augment(pg[0], pg[1], d, rng, 30)
            consider(tn, te)
        return best

    # D >= 4: generalized quadrangle base plus twin augmentation.
    if D >= 4:
        qs = [q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)]
        if qs:
            q = qs[0]
            gn, ge = _gq_w(q)
            consider(gn, ge)
            tn, te = _twin_augment(gn, ge, d, rng, 30)
            consider(tn, te)

    # Bold search: bi-Cayley graphs over non-cyclic semidirect products.
    deadline = start + 0.80 * time_limit
    while time.monotonic() < deadline and best_n < moore:
        lo = max(d, best_n // 2 + 1)
        G = rng.randint(lo, lo + 30)
        g = _pick_group(G, rng)
        if g is None:
            continue
        m, k, r = g
        try:
            G, mt, iv = _group_tables(m, k, r)
        except ValueError:
            continue
        S = _haar_search(d, D, G, mt, iv, rng, deadline, 800)
        if S is not None:
            n, e = _haar_edges(G, mt, S)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
