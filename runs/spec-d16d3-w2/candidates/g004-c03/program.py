"""Diameter-3 bipartite construction: PG(2,q) incidence plus independent weighted twin layers.

Construction (D = 3):
  * Start from the incidence graph of PG(2,q), with points 0..m-1 and lines m..2m-1.
    Each vertex has degree q+1, so it has spare capacity s = d - q - 1.
  * Point-side layer: choose multiplicities mu_P >= 0 on points so that for every line L,
    sum_{P on L} mu_P <= s. Each unit of mu_P becomes a new vertex x adjacent to all q+1
    lines through P.
  * Line-side layer: choose multiplicities nu_L >= 0 on lines so that for every point Q,
    sum_{L through Q} nu_L <= s. Each unit becomes a new vertex y adjacent to all q+1 points on L.

Why the diameter stays <= 3: two new point-side vertices share the line PQ. A point-side
vertex and a point are at distance <= 2 through a line. A point-side vertex and a line are at
distance <= 3 through a line through P meeting L. The line-side case is symmetric, and the
mixed pairs are at distance <= 3 by the same kind of argument. Bipartiteness holds since
point-side vertices attach only to lines and line-side vertices attach only to points.

The layers are independent, so the order is 2m + W_A + W_B, where W_A and W_B are the total
weights. The LP bound is W <= s*m/(q+1) per side. For d=16, q=13 this gives 366 + 52 = 418,
and the record 394 corresponds to 0/1 weights (conic arcs). The search uses integer weights
with local search and plateau moves. Every result is checked with lib.is_valid, and a valid
K_{d,d} or plain PG incidence is kept as the fallback.
"""
import random
import time

import lib


def _incidence_lists(m, edges):
    """Point-to-line and line-to-point lists for the PG incidence graph (points < m <= lines)."""
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        a, b = (u, v) if u < v else (v, u)
        pl[a].append(b - m)
        lp[b - m].append(a)
    return pl, lp


def _weights(m, cons, s, rng, deadline):
    """Integer weights mu on items 0..m-1 with every constraint j having sum_{i: j in cons[i]} mu_i <= s.

    Returns (total, mu) for the best solution found before the deadline.
    Moves: add a unit where feasible; otherwise move one unit from a blocking item to i
    (a plateau move that keeps the total). Occasionally a net loss is kept to escape.
    """
    members = [[] for _ in range(m)]
    for i, c in enumerate(cons):
        for j in c:
            members[j].append(i)
    mu = [0] * m
    load = [0] * m
    total = 0
    best_total = 0
    best = [0] * m
    it = 0
    while True:
        it += 1
        if (it & 1023) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(m)
        if mu[i] >= s:
            continue
        ci = cons[i]
        if all(load[j] < s for j in ci):
            mu[i] += 1
            for j in ci:
                load[j] += 1
            total += 1
            if total > best_total:
                best_total = total
                best = mu[:]
            continue
        sat = [j for j in ci if load[j] >= s]
        j = rng.choice(sat)
        cand = [k for k in members[j] if mu[k] > 0 and k != i]
        if not cand:
            continue
        k = rng.choice(cand)
        ck = cons[k]
        mu[k] -= 1
        for t in ck:
            load[t] -= 1
        total -= 1
        if all(load[t] < s for t in ci):
            mu[i] += 1
            for t in ci:
                load[t] += 1
            total += 1
        elif rng.random() >= 0.02:
            mu[k] += 1
            for t in ck:
                load[t] += 1
            total += 1
        if total > best_total:
            best_total = total
            best = mu[:]
    return best_total, best


def _assemble(m, base_edges, pl, lp, mu_a, nu_b):
    """Attach mu_a[P] point-side copies to lines through P and nu_b[L] line-side copies to points on L."""
    n = 2 * m + sum(mu_a) + sum(nu_b)
    edges = list(base_edges)
    nxt = 2 * m
    for P in range(m):
        for _ in range(mu_a[P]):
            x = nxt
            nxt += 1
            for L in pl[P]:
                edges.append((x, m + L))
    for L in range(m):
        for _ in range(nu_b[L]):
            y = nxt
            nxt += 1
            for Q in lp[L]:
                edges.append((Q, y))
    return nxt, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D < 3:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    deadline = start + 0.6 * time_limit
    # Prime powers q with q + 1 <= d.
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
    if not qs:
        return best

    # Plain PG(2, q) incidence for the largest usable q (diameter 3).
    n2, e2 = lib.projective_plane_incidence(qs[0])
    consider(n2, e2)

    # Weighted twin layers: only candidates whose counting bound can beat the current best.
    cands = []
    for q in qs:
        s = d - q - 1
        m = q * q + q + 1
        if s < 1:
            continue
        bound = 2 * m + 2 * ((s * m) // (q + 1))
        if bound > best_n:
            cands.append((bound, q, s))
    cands.sort(reverse=True)

    for idx, (bound, q, s) in enumerate(cands):
        if bound <= best_n:
            continue
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(cands) - idx)
        n2, E = lib.projective_plane_incidence(q)
        m = n2 // 2
        pl, lp = _incidence_lists(m, E)
        half = share / 2.0
        _, mu_a = _weights(m, pl, s, random.Random(seed * 1000003 + q * 17 + 1),
                           time.monotonic() + half)
        _, nu_b = _weights(m, lp, s, random.Random(seed * 1000003 + q * 17 + 2),
                           time.monotonic() + half)
        n, EE = _assemble(m, E, pl, lp, mu_a, nu_b)
        consider(n, EE)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
