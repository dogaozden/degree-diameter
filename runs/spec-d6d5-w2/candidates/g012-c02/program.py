import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane, Araujo-Pardo-Lopez (D = 3), and the
# generalized quadrangle W(q) (D = 4). The fallback is K_{d,d}.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New main family for D >= 5: bi-Cayley graphs over small groups.
#
# Group G of order g acts regularly on A = {a_x} and B = {b_x}.
# Connection set S (|S| = d) gives edges a_x ~ b_{x*s} for s in S.
# Each vertex has degree exactly d, the graph is bipartite, and no edge repeats.
#
# Left multiplication by G is an automorphism that is transitive on A and on B.
# So the diameter is at most D iff BFS from a_e and from b_e reaches every
# vertex within D steps. That is an O(g*d) check, much cheaper than full APSP.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k of order G (k = 1 gives cyclic). Returns (order, mul, inv) or None."""
    divs = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(40):
        k = rng.choice(divs)
        m = G // k
        if k == 1:
            r = 1
        else:
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        return order, mul, inv
    return None


def _cost(G, mt, invt, S, D):
    """Total number of vertices not reached within D from a_e and from b_e (zero iff valid).

    Vertex a_x has index x; b_x has index G + x. Identity has index 0.
    Neighbours: a_x ~ b_{x s}, so from b_h the neighbours are a_{h s^{-1}}.
    """
    invS = [invt[s] for s in S]
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
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
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _anneal(G, mt, invt, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S of size d. Returns (S or None, cost)."""
    if G < d:
        return None, 0
    S = rng.sample(range(G), d)
    cur = _cost(G, mt, invt, S, D)
    T = 2.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c = _cost(G, mt, invt, S, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            S[i] = old
        T = max(0.3, T * 0.997)
    return (list(S) if cur == 0 else None), cur


def _bicayley_edges(G, mt, S):
    """Edges of the bi-Cayley graph: a_x = x, b_y = G + y, joined when y = x*s."""
    E = []
    for x in range(G):
        row = mt[x]
        for s in S:
            E.append((x, G + row[s]))
    return 2 * G, E


def _bicayley_search(d, D, G0, deadline, rng):
    """Galloping search for the largest valid bi-Cayley graph. Returns (n, edges) or None."""
    best = None
    best_G = max(G0, d + 1)
    step = max(1, best_G // 16)
    while time.monotonic() < deadline:
        G = best_G + step
        found = None
        for _ in range(4):
            if time.monotonic() >= deadline:
                break
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul, inv = g
            mt = [[mul(x, y) for y in range(order)] for x in range(order)]
            invt = [inv(x) for x in range(order)]
            S, _c = _anneal(order, mt, invt, d, D, rng, deadline, 1200)
            if S is not None:
                found = (order, mt, S)
                break
        if found is not None:
            order, mt, S = found
            n, e = _bicayley_edges(order, mt, S)
            if lib.is_valid(n, e, d, D):
                best = (n, e)
                best_G = order
                step = min(step * 2, best_G // 8 + 1)
                continue
        step = max(1, step // 2)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
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

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])

        if D == 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        if D >= 5 and d >= 2:
            res = _bicayley_search(d, D, best_n // 2, deadline, rng)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
