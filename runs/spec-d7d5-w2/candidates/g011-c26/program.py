import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact algebraic constructions (kept from the parent as baselines).
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
# NEW construction: single-block bi-Cayley graphs over groups.
#
# Group G = Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a+r^b c, b+e)).
# Vertices A_g and B_h (g, h in G). Connection set S of d distinct elements:
#     A_g ~ B_{g*s}  for every s in S.
# Left multiplication is an automorphism, so the diameter is at most D iff the
# radius-D balls around A_e and B_e both cover the whole graph. The search is
# simulated annealing over S with cost = number of unreached (source, vertex)
# pairs, evaluated by vectorised BFS over the group table. Groups are sampled
# near the target order, with a strong preference for non-abelian groups.
# Every accepted result is re-checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def _divisors(n):
    ds = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n // i:
                ds.append(n // i)
        i += 1
    return sorted(ds)


def _sample_group(G, rng):
    """Return (m, k2, r) with m * k2 = G, m >= 2, and r^k2 = 1 mod m, gcd(r, m) = 1."""
    divs = [k for k in _divisors(G) if k >= 2 and G // k >= 2]
    if divs and rng.random() < 0.8:
        k2 = rng.choice(divs)
    else:
        k2 = 1
    m = G // k2
    r = 1 % m
    if k2 > 1:
        for _ in range(80):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    return m, k2, r


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _cost(G, Ts, Invs, S, D):
    """Total unreached (source, vertex) pairs for sources A_e and B_e within radius D."""
    total = 0
    for side in (0, 1):
        visA = np.zeros(G, dtype=bool)
        visB = np.zeros(G, dtype=bool)
        if side == 0:
            visA[0] = True
        else:
            visB[0] = True
        fa = np.flatnonzero(visA)
        fb = np.flatnonzero(visB)
        for _ in range(D):
            nb = np.zeros(G, dtype=bool)
            for s in S:
                nb[Ts[s][fa]] = True
            nb &= ~visB
            na = np.zeros(G, dtype=bool)
            for s in S:
                na[Invs[s][fb]] = True
            na &= ~visA
            visB |= nb
            visA |= na
            fa = np.flatnonzero(na)
            fb = np.flatnonzero(nb)
            if fa.size == 0 and fb.size == 0:
                break
        total += 2 * G - int(visA.sum()) - int(visB.sum())
    return total


def _anneal(G, Ts, Invs, d, D, rng, deadline, iters):
    """Simulated annealing over the connection set S. Returns S if cost 0 is reached, else None."""
    if d > G:
        return None
    S = rng.sample(range(G), d)
    cur = _cost(G, Ts, Invs, S, D)
    best_cost, best_S = cur, list(S)
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 3.0 * (1.0 - t / iters) + 0.2
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cost(G, Ts, Invs, S, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
            if cur < best_cost:
                best_cost, best_S = cur, list(S)
        else:
            S[i] = old
    return best_S if best_cost == 0 else None


def _graph_from(G, Ts, S):
    """Edges of the bi-Cayley graph: A_g = g, B_h = G + h, A_g ~ B_{g*s} for s in S."""
    edges = []
    for s in S:
        row = Ts[s]
        for g in range(G):
            edges.append((g, G + int(row[g])))
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Greedy pair insertion (kept from the parent, with a consecutive-failure cap).
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of the graph, or None if it is not bipartite."""
    adj = lib.adjacency(n, edges)
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
                elif color[v] == color[u]:
                    return None
    return color


def _extend(n, edges, d, D, rng, deadline, max_fail=40):
    """Grow the order by 2 per accepted step: remove d-1 pairwise-disjoint edges, add x ~ b_i, y ~ a_i, x ~ y."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fail:
        order = list(range(len(edges)))
        rng.shuffle(order)
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
            fails = 0
        else:
            fails += 1
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    search_deadline = start + 0.82 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # New search: single-block bi-Cayley graphs over groups near the target order.
    if D >= 3:
        lo = best_n // 2 + 1
        while time.monotonic() < search_deadline:
            G = lo + int((rng.random() ** 2) * 24)
            if G < 2:
                G = 2
            m, k2, r = _sample_group(G, rng)
            Gr, Ts, Invs = _semidirect_tables(m, k2, r)
            S = _anneal(Gr, Ts, Invs, d, D, rng, search_deadline, 3000)
            if S is not None:
                n_new, e_new = _graph_from(Gr, Ts, S)
                if n_new > best_n and lib.is_valid(n_new, e_new, d, D):
                    best = (n_new, e_new)
                    best_n = n_new
                    lo = best_n // 2 + 1

    # Greedy pair insertion on the best graph found.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
