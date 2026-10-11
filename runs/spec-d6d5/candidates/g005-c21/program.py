import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (kept as fallbacks; each result is re-checked).
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
# Family A (new, main search): Haar graphs H(G, S) over groups of order m.
#
# Vertices a_g (0..m-1) and b_h (m..2m-1); a_g ~ b_{g*s} for s in S, |S| = d.
# Left multiplication is an automorphism, so each side is one orbit. Therefore
# diameter <= D iff BFS from a_0 and from b_0 (depth D) reaches all 2m vertices.
# The group pool includes cyclic, direct-product and semidirect groups, and the
# evaluator is a plain two-BFS count, so each step costs about a millisecond.
# ----------------------------------------------------------------------------

def _sample_group(m, rng):
    """Random group of order m as (order, mul, inv): Z_a x|_r Z_k with a * k = m."""
    k = rng.choice([x for x in range(1, m + 1) if m % x == 0])
    a = m // k
    if k == 1 or a == 1:
        r = 1
    else:
        cands = [r for r in range(1, a)
                 if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a]
        if not cands:
            return None
        r = rng.choice(cands)  # r = 1 always qualifies: a direct product
    try:
        order, mul, inv = lib.semidirect_group(a, k, r)
    except ValueError:
        return None
    return order, mul, inv


class _Haar:
    """Haar graph of a group of order m with cached right-multiplication rows."""

    def __init__(self, m, mul, inv):
        self.m = m
        self.mul = mul
        self.inv = inv
        self.rows = {}

    def row(self, s):
        """rA[g] = B-index of a_g's neighbour via s; rB[h] = A-index of b_h's neighbour via s."""
        r = self.rows.get(s)
        if r is None:
            m, mul = self.m, self.mul
            si = self.inv(s)
            rA = [m + mul(g, s) for g in range(m)]
            rB = [mul(h, si) for h in range(m)]
            r = (rA, rB)
            self.rows[s] = r
        return r

    def cost(self, S, D):
        """Number of vertices not reached within D from a_0 and from b_0 (zero means valid)."""
        m = self.m
        rs = [self.row(s) for s in S]
        As = [r[0] for r in rs]
        Bs = [r[1] for r in rs]
        total = 0
        for src in (0, m):
            seen = bytearray(2 * m)
            seen[src] = 1
            frontier = [src]
            count = 1
            for _ in range(D):
                nxt = []
                for x in frontier:
                    if x < m:
                        for rA in As:
                            y = rA[x]
                            if not seen[y]:
                                seen[y] = 1
                                nxt.append(y)
                    else:
                        h = x - m
                        for rB in Bs:
                            y = rB[h]
                            if not seen[y]:
                                seen[y] = 1
                                nxt.append(y)
                if not nxt:
                    break
                count += len(nxt)
                frontier = nxt
            total += 2 * m - count
        return total

    def edges(self, S):
        m = self.m
        E = []
        for s in S:
            rA, _ = self.row(s)
            for g in range(m):
                E.append((g, rA[g]))
        return 2 * m, E


def _anneal_haar(H, d, D, rng, iters, deadline):
    """Simulated annealing over the connection set S (d distinct group elements)."""
    m = H.m
    S = rng.sample(range(m), d)
    cost = H.cost(S, D)
    best, bestS = cost, list(S)
    for t in range(iters):
        if best == 0 or time.monotonic() > deadline:
            break
        T = 1.5 * (1.0 - t / iters) + 0.05
        i = rng.randrange(d)
        new = rng.randrange(m)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = H.cost(S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best:
                best, bestS = cost, list(S)
        else:
            S[i] = old
    return best, bestS


# ----------------------------------------------------------------------------
# Family B (secondary): voltage lifts over semidirect products with k base
# vertices per side, searched by annealing (kept from the parent program).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_lift_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
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


def _lift_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _lift_cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _lift_search(d, D, k, G, rng, iters, deadline):
    g = _sample_lift_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_lift_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)

    best_cost = cost
    best_darts = [list(x) for x in darts]
    best_perms = list(perms)

    T0 = 3.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _lift_perm(mul, G, new_s)
        c2 = _lift_cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
                best_perms = list(perms)
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if best_cost == 0:
        return _lift_edges(k, G, best_darts, best_perms)
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 3.0)
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main loop: mostly Haar-graph search aimed just above the current best order,
    # with a minority of voltage-lift attempts for diversity.
    while time.monotonic() < deadline:
        if rng.random() < 0.7:
            m = best_n // 2 + 1 + rng.randrange(3)
            if m < d:
                m = d
            grp = _sample_group(m, rng)
            if grp is None:
                continue
            H = _Haar(*grp)
            c, S = _anneal_haar(H, d, D, rng, 1500, deadline)
            if c == 0:
                n, e = H.edges(S)
                consider(n, e)
        else:
            k = rng.choice([1, 1, 2, 2, 3])
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
            res = _lift_search(d, D, k, G, rng, 1500, deadline)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
