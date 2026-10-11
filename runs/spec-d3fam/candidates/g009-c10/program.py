import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known bases: projective plane, Araujo-Pardo & Lopez, generalized quadrangle.
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bold new family: bipartite Cayley graphs A_g ~ B_{g s}, s in S, over groups
# of order G (cyclic or Z_m x| Z_k). Such a graph has order 2G.
#
# Left multiplication by h is an automorphism that is transitive on each side,
# so diameter <= D holds iff A_e and B_e both reach every vertex within D steps.
# That makes the cost evaluation cheap: two BFS runs per candidate S.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random group of order G with identity 0."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 8, 10, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            continue  # handled by the cyclic branch below
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
    return G, (lambda x, y: (x + y) % G)


def _tables(G, mul):
    """Multiplication table T[g][s] = g*s and the inverse of each element."""
    T = [[mul(g, s) for s in range(G)] for g in range(G)]
    inv = [0] * G
    for g in range(G):
        row = T[g]
        for h in range(G):
            if row[h] == 0:
                inv[g] = h
                break
    return T, inv


def _cost(S, G, T, inv, D):
    """Number of vertices not within D of A_e or of B_e. Zero means valid."""
    N = 2 * G
    sinv = [inv[s] for s in S]
    adj = [None] * N
    for g in range(G):
        Tg = T[g]
        adj[g] = [G + Tg[s] for s in S]
    for h in range(G):
        Th = T[h]
        adj[G + h] = [Th[si] for si in sinv]

    def unreached(src):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        return N - cnt

    return unreached(0) + unreached(G)


def _anneal(d, D, G, mul, rng, deadline):
    """Simulated annealing over the connection set S of size d; returns (S, T) or None."""
    T, inv = _tables(G, mul)
    S = rng.sample(range(G), d)
    c = _cost(S, G, T, inv, D)
    if c == 0:
        return S, T
    temp = 3.0
    while time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cost(S, G, T, inv, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
            if c == 0:
                return S, T
        else:
            S[i] = old
        temp = max(0.05, temp * 0.999)
    return None


def _cayley_edges(G, S, T):
    return [(g, G + T[g][s]) for g in range(G) for s in S]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed * 1000003 + d * 101 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Moore-optimal case for D = 3: PG(2, d-1) incidence graph.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except (ValueError, StopIteration, KeyError):
            pass

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New search: bipartite Cayley graphs over annealed connection sets.
    # Each attempt targets order 2G with G just above the current best half-order.
    try:
        while time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            chunk = min(remaining, max(1.5, remaining / 4.0))
            G = best_n // 2 + 1
            if d > G:
                break
            order, mul = _sample_group(G, rng)
            res = _anneal(d, D, order, mul, rng, time.monotonic() + chunk)
            if res is not None:
                S, T = res
                consider(2 * order, _cayley_edges(order, S, T))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
