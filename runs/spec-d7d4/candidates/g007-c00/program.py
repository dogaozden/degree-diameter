import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: generalized quadrangle W(q) for D = 4 and projective planes for D = 3.
# ----------------------------------------------------------------------------

def _largest_pp(limit):
    """Largest prime power q with 2 <= q <= limit, or None."""
    for q in range(limit, 1, -1):
        if lib.is_prime_power(q):
            return q
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
# Bi-Cayley search (new): a single group G acting regularly on both sides.
#
# Vertices a_x (id x) and b_y (id G + y). Edges a_x ~ b_{x*s} for s in S, |S| = d.
# Left multiplication by h is an automorphism, so the diameter check only needs
# BFS from a_e (id 0) and b_e (id G). Cost = number of unreached (source, vertex)
# pairs within radius D, summed over the two sources. Zero means valid.
# ----------------------------------------------------------------------------

def _group_options(G):
    """All (m, k, r) with Z_m x| Z_k of order G (k = 1 gives the cyclic group)."""
    opts = []
    for k in range(1, 13):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _cost(G, S, mt, inv, D):
    Sinv = [inv[s] for s in S]
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
                    for si in Sinv:
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


def _anneal(G, d, D, mt, inv, rng, deadline):
    """Anneal a size-d connection set S in G until the bi-Cayley graph has diameter D."""
    S = rng.sample(range(G), d)
    c = _cost(G, S, mt, inv, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while c > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 0.8 * (0.02 ** frac)
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        T_S = S[:]
        T_S[i] = new
        c2 = _cost(G, T_S, mt, inv, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T_S, c2
    return S if c == 0 else None


def _bicayley_search(d, D, best_n, rng, deadline):
    """Yield (n, edges) candidates from bi-Cayley graphs of order 2G > best_n."""
    G_hi = lib._moore_bound(d, D) // 2
    results = []
    while time.monotonic() < deadline:
        G_lo = best_n // 2 + 1
        if G_lo > G_hi:
            break
        G = G_lo + rng.randrange(40)
        if G < d:
            continue
        opts = _group_options(G)
        if not opts:
            continue
        m, k, r = rng.choice(opts)
        order, mul, inv_fn = lib.semidirect_group(m, k, r)
        inv = [inv_fn(x) for x in range(order)]
        mt = [[mul(x, y) for y in range(order)] for x in range(order)]
        slice_end = min(deadline, time.monotonic() + 2.0)
        S = _anneal(order, d, D, mt, inv, rng, slice_end)
        if S is not None:
            edges = [(x, order + mt[x][s]) for x in range(order) for s in S]
            results.append((2 * order, edges))
            best_n = max(best_n, 2 * order)
    return results


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D == 3:
        q = _largest_pp(d - 1)
        if q is not None:
            consider(*lib.projective_plane_incidence(q))

    if D == 4:
        q = _largest_pp(min(d - 1, 9))
        if q is not None:
            consider(*_gq_w(q))

    # New construction: bi-Cayley graphs over Z_m x| Z_k of order just above the
    # current best, annealed to diameter D.
    if D in (3, 4):
        for n_c, e_c in _bicayley_search(d, D, best_n, rng, deadline):
            consider(n_c, e_c)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
