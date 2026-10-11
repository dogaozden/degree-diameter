"""Diameter-3 bipartite graphs from PG(2,q) plus two families of extra vertices.

Idea (new relative to the parent): the polarity of PG(2,q) (point i <-> line i, same
coordinate vector) is an automorphism of the incidence graph. So one family F of k index
sets, each of size d, serves both sides:
  * A-vertex i is joined to the lines {c : c in F_i}, and
  * B-vertex i is joined to the points {c : c in F_i}.
Every member F_i must cover all points (for each vector v some c in F_i has v.c = 0),
any two members must share an index, and each index may lie in at most s = d-q-1 members,
which keeps all degrees <= d. Then the graph has order 2(q^2+q+1) + 2k and diameter 3.
The conic (oval) family gives k = q+1, which reproduces the known record for d = 16.
Simulated annealing then searches for k = q+2 .. d+1, which can beat it. Every candidate
is checked with lib.is_valid before it is kept.
"""
import math
import random
import time

import lib


def _largest_pp_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _base(q):
    """PG(2,q) incidence: points 0..m-1, lines m..2m-1. Also the per-point and per-line lists."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    lines_through = [[] for _ in range(m)]  # point -> line indices
    pts_on = [[] for _ in range(m)]         # line index -> point indices
    for u, v in edges:
        lines_through[u].append(v - m)
        pts_on[v - m].append(u)
    return m, list(edges), lines_through, pts_on, pts, index


def _conic_family(q, index, lines_through):
    """Pencils at the q+1 points of a conic (an oval, q odd): each line carries <= 2 of them."""
    F = lib.GF(q)
    conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    return [list(lines_through[c]) for c in conic]


def _assemble(m, base_edges, family):
    """Add A-vertices (adjacent to lines) and B-vertices (adjacent to points) for each member."""
    k = len(family)
    n = 2 * m + 2 * k
    edges = list(base_edges)
    for i, S in enumerate(family):
        a = 2 * m + i
        for c in S:
            edges.append((a, m + c))
    for i, S in enumerate(family):
        b = 2 * m + k + i
        for c in S:
            edges.append((c, b))
    return n, edges


def _anneal(k, size, cap, cover, coverers, nu, rng, deadline):
    """Find k subsets F_i of range(nu), each of size `size`, such that:
    every F_i covers all nu elements (cover[c] lists elements covered by candidate c),
    every pair F_i, F_j shares a candidate, and every candidate lies in <= cap sets.
    Returns the family as sorted lists, or None on timeout."""
    nc = nu
    sel = [set(rng.sample(range(nc), size)) for _ in range(k)]
    memb = [set() for _ in range(nc)]
    load = [0] * nc
    cc = [[0] * nu for _ in range(k)]
    for i in range(k):
        for c in sel[i]:
            memb[c].add(i)
            load[c] += 1
            for u in cover[c]:
                cc[i][u] += 1
    inter = [[0] * k for _ in range(k)]
    for i in range(k):
        for j in range(i + 1, k):
            x = len(sel[i] & sel[j])
            inter[i][j] = inter[j][i] = x
    pen = sum(1 for i in range(k) for u in range(nu) if cc[i][u] == 0)
    pen += sum(max(0, x - cap) for x in load)
    pen += sum(1 for i in range(k) for j in range(i + 1, k) if inter[i][j] == 0)

    def apply(i, a, b):
        """Replace candidate a by b in member i; return the change in penalty."""
        delta = 0
        ci = cc[i]
        for u in cover[a]:
            ci[u] -= 1
            if ci[u] == 0:
                delta += 1
        for u in cover[b]:
            if ci[u] == 0:
                delta -= 1
            ci[u] += 1
        sel[i].discard(a)
        sel[i].add(b)
        L = load[a]
        if L > cap:
            delta -= 1
        load[a] = L - 1
        memb[a].discard(i)
        for j in memb[a]:
            x = inter[i][j] - 1
            inter[i][j] = x
            inter[j][i] = x
            if x == 0:
                delta += 1
        L = load[b]
        if L >= cap:
            delta += 1
        load[b] = L + 1
        for j in memb[b]:
            x = inter[i][j]
            if x == 0:
                delta -= 1
            inter[i][j] = x + 1
            inter[j][i] = x + 1
        memb[b].add(i)
        return delta

    T0, T1 = 0.6, 0.05
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T = T0
    it = 0
    while pen > 0:
        it += 1
        if (it & 255) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            T = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        i = rng.randrange(k)
        si = sel[i]
        a = rng.choice(tuple(si))
        if rng.random() < 0.7:
            # Bias the incoming candidate toward an element member i does not yet cover.
            ci = cc[i]
            u = rng.randrange(nu)
            for _ in range(8):
                if ci[u] == 0:
                    break
                u = rng.randrange(nu)
            b = rng.choice(coverers[u])
        else:
            b = rng.randrange(nc)
        if b in si:
            continue
        delta = apply(i, a, b)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            pen += delta
        else:
            apply(i, b, a)
    return [sorted(s) for s in sel]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = min(0.8 * float(time_limit), 48.0)
    deadline = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_E = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D >= 3:
        q = _largest_pp_at_most(d - 1)
        if q is not None and q >= 2:
            m, base_E, lt, po, pts, index = _base(q)
            consider(2 * m, base_E)
            s = d - q - 1
            if s >= 2 and q % 2 == 1:
                fam0 = _conic_family(q, index, lt)
                n, E = _assemble(m, base_E, fam0)
                consider(n, E)
            if s >= 1:
                rng = random.Random(seed * 1000003 + 97 * d + D)
                k = q + 2
                kmax = min(d + 1, m)
                while k <= kmax:
                    now = time.monotonic()
                    remaining = deadline - now
                    if remaining <= 0.5:
                        break
                    dl = deadline if k >= kmax else now + 0.35 * remaining
                    fam = _anneal(k, d, s, po, lt, m, rng, dl)
                    if fam is None:
                        break
                    n, E = _assemble(m, base_E, fam)
                    consider(n, E)
                    k += 1

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
