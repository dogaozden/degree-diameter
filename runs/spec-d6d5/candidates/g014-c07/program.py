import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines: projective plane, Araujo-Pardo-Lopez, generalized quadrangle.
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW HELPER: tabu search over bi-Cayley graphs B(G, S).
#
# Vertices A_g = g and B_h = G + h for g, h in a group G of order `order`.
# A connection set S (|S| = d, distinct elements) gives edges A_g -- B_{g*s}.
# Left multiplication by x maps A_g -> A_{xg}, B_h -> B_{xh}, so the graph is
# vertex-transitive on each side. Hence diameter <= D holds iff the two BFS
# balls from A_e and B_e cover everything within D steps.
#
# Cost = number of (source, vertex) pairs still unreached (zero means valid).
# Search: tabu over the d connection elements, with a sampled neighbourhood
# and a tenure on recently removed elements.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul, inv) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(100):
        k2 = rng.choice(choices)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul, inv
    return None


def _cost_k1(S, Rs, Rinv_of, G, D):
    """Unreached (source, vertex) pairs over sources A_e and B_e within distance D.

    Rs[s][g] = g*s.  Edge A_g -- B_{g s}; B_h -- A_{h s^-1}, i.e. Rs[inv(s)][h].
    """
    N = 2 * G
    Rs_S = [Rs[s] for s in S]
    Ri_S = [Rinv_of[s] for s in S]
    total = 0
    for src in (0, G):
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for R in Rs_S:
                        v = R[u] + G
                        if not seen[v]:
                            seen[v] = True
                            nxt.append(v)
                else:
                    x = u - G
                    for R in Ri_S:
                        v = R[x]
                        if not seen[v]:
                            seen[v] = True
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _tabu_k1(d, D, G, Rs, Rinv_of, rng, deadline, steps, cands_per_step=16):
    """Tabu search for a connection set S of d distinct group elements with zero cost."""
    S = rng.sample(range(G), d)
    cost = _cost_k1(S, Rs, Rinv_of, G, D)
    best_c, best_S = cost, S[:]
    tabu = {}
    for t in range(steps):
        if best_c == 0 or time.monotonic() > deadline:
            break
        cand_best = None
        for _ in range(cands_per_step):
            i = rng.randrange(d)
            new = rng.randrange(G)
            if new in S:
                continue
            T = S[:]
            T[i] = new
            c = _cost_k1(T, Rs, Rinv_of, G, D)
            if tabu.get(new, -1) > t and c >= best_c:
                continue
            if (cand_best is None or c < cand_best[0]
                    or (c == cand_best[0] and rng.random() < 0.5)):
                cand_best = (c, i, new, T)
        if cand_best is None:
            continue
        c, i, new, T = cand_best
        tabu[S[i]] = t + 5 + rng.randrange(5)
        S, cost = T, c
        if cost < best_c:
            best_c, best_S = cost, S[:]
    return best_c, best_S


def _edges_k1(G, Rs, S):
    """Edges of B(G, S): A_g -- B_{g s} for s in S."""
    E = []
    for s in S:
        R = Rs[s]
        for g in range(G):
            E.append((g, G + R[g]))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Haar graph hill-climb for small D (cyclic lifts; secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, iters):
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # d = 2: the cycle C_{2D} has diameter D.
    if d == 2 and D >= 2:
        consider(*lib.haar_graph(D, [0, 1]))

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

    # Small D: cyclic Haar-graph hill-climb over increasing Z_m.
    if D <= 4 and d >= 3:
        haar_deadline = start + 0.3 * time_limit
        m = d + 1
        while time.monotonic() < haar_deadline:
            S = _search_haar(d, D, m, rng, 120)
            if S is not None:
                consider(*lib.haar_graph(m, S))
            m += 1
            if m > 6 * d + 40:
                break

    # Main search for D >= 5: tabu over bi-Cayley graphs of semidirect products.
    if D >= 5 and d >= 3:
        main_deadline = start + 0.82 * time_limit
        lo = max(d, best_n // 2 + 1)
        hi = lo + max(4, lo // 20)
        per_group = 8.0
        while time.monotonic() < main_deadline:
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                lo += 1
                hi = max(hi, lo + 2)
                continue
            order, mul, inv_f = g
            Rinv_of_all = None
            Rs = [[mul(x, s) for x in range(order)] for s in range(order)]
            inv = [inv_f(s) for s in range(order)]
            Rinv_of = [Rs[inv[s]] for s in range(order)]
            dl = min(main_deadline, time.monotonic() + per_group)
            c, S = _tabu_k1(d, D, order, Rs, Rinv_of, rng, dl, 250)
            if c == 0:
                n, e = _edges_k1(order, Rs, S)
                if n > best_n:
                    consider(n, e)
                # Successful order: move the window above it.
                lo = max(lo, order + 1)
                hi = lo + max(4, lo // 20)
            else:
                # Failed: drift the window slightly while keeping it near the target.
                if rng.random() < 0.5:
                    lo += 1
                    hi = max(hi, lo + 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
