import itertools
import math
import random
import time

import lib


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bold new construction: bipartite Cayley-type graphs (single base pair).
#
# Group G of order m. A-vertices g in [0, G), B-vertices G + h.
# Connection set S = {s_1..s_d}, a set of d distinct group elements.
# Edges: A_g -- B_{g*s} for s in S. Every vertex has degree exactly d and the
# graph is bipartite automatically.
#
# Symmetry: left multiplication is an automorphism that is transitive on the
# A-side and on the B-side. So diameter <= D holds iff BFS from A_e and from
# B_e each reach all 2G vertices within D steps. The search is simulated
# annealing over S inside semidirect products Z_m x| Z_k (nonabelian allowed),
# with the number of unreached vertices as the cost.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul, inv) for a random semidirect product Z_m x| Z_k of order G, or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(40):
        k = rng.choice(divs)
        m = G // k
        if k == 1:
            r = 1
        else:
            r = None
            for _t in range(60):
                c = rng.randrange(1, m)
                if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        return order, mul, inv
    return None


def _cost(G, D, fw, bw):
    """Number of (source, vertex) pairs not reached within D steps, sources A_e and B_e."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for p in fw:
                        v = G + p[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for p in bw:
                        v = p[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _climb(d, D, G, mul, inv, rng, iters, deadline):
    """Annealing over connection sets S of size d in a group of order G (requires G > d).

    Returns (found, S, best_cost).
    """
    fcache = {}
    bcache = {}

    def fwd(s):
        p = fcache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            fcache[s] = p
        return p

    def bwd(s):
        p = bcache.get(s)
        if p is None:
            si = inv(s)
            p = [mul(h, si) for h in range(G)]
            bcache[s] = p
        return p

    S = rng.sample(range(G), d)

    def evaluate(S):
        return _cost(G, D, [fwd(s) for s in S], [bwd(s) for s in S])

    cur = evaluate(S)
    best = cur
    bestS = list(S)
    T0 = 2.0
    for t in range(iters):
        if best == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        i = rng.randrange(d)
        old = S[i]
        while True:
            new = rng.randrange(G)
            if new not in S:
                break
        S[i] = new
        c = evaluate(S)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
            if c < best:
                best = c
                bestS = list(S)
        else:
            S[i] = old
    return best == 0, bestS, best


def _edges_from(G, mul, S):
    """Edge list of the Cayley-type bipartite graph on A_g = g, B_h = G + h."""
    E = []
    for g in range(G):
        for s in S:
            E.append((g, G + mul(g, s)))
    return 2 * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Stay well inside the limit: use at most 85% and leave at least 3 seconds spare.
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases that already meet the Moore bound return immediately.
    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best

    # Main search: Cayley-type bipartite graphs over nonabelian/cyclic groups.
    # Always aim one group order above the current best (n = 2G > best_n).
    attempts = 0
    while time.monotonic() < deadline:
        G = max(d + 1, best_n // 2 + 1)
        if 2 * G >= moore and best_n >= moore:
            break
        grp = _sample_group(G, rng)
        if grp is None:
            # No usable group of this order; nudge upward so a different order is tried.
            G += 1
            if time.monotonic() >= deadline:
                break
            continue
        order, mul, inv = grp
        attempts += 1
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        found, S, _ = _climb(d, D, G, mul, inv, rng, 1500, deadline)
        if found:
            n, e = _edges_from(G, mul, S)
            consider(n, e)
        if best_n >= moore:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
