"""Bold variant: random degree-preserving voltage lifts over small bipartite base
graphs (cyclic or semidirect groups), searched by hill climbing on the number of
pairs at distance > D. A verified generalized-quadrangle or projective-plane
incidence graph (or K_{d,d}) is kept as the fallback, and every stored graph is
checked with lib.is_valid."""

import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallback base graphs.
# ----------------------------------------------------------------------------

def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q); diameter 4."""
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
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Voltage lifts over groups, searched by hill climbing.
#
# Base graph: k "A" vertices and k "B" vertices, with k*d darts. Every A vertex
# gets d darts, and every B vertex gets d darts (a random multigraph). Each dart
# carries a group element. The lift has 2*k*|G| vertices and stays bipartite.
# Moves: change one voltage, or do a degree-preserving double swap of endpoints.
# The cost is the number of unordered vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _random_mul(G, rng):
    """Multiplication of a random group of order G (semidirect product or cyclic)."""
    divs = [k2 for k2 in range(2, G) if G % k2 == 0 and G // k2 >= 2]
    if divs and rng.random() < 0.6:
        k2 = rng.choice(divs)
        m = G // k2
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            return lib.semidirect_group(m, k2, rng.choice(rs))[1]
    return lib.cyclic_group(G)[1]


def _lift(k, G, mul, darts):
    """Edges of the lift: dart (u, v, g) joins A-block u to B-block v over the group."""
    edges = set()
    for u, v, g in darts:
        kv = (k + v) * G
        for x in range(G):
            a = u * G + x
            b = kv + mul(x, g)
            edges.add((a, b) if a < b else (b, a))
    return sorted(edges)


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D, via bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _climb(k, G, mul, d, D, rng, deadline, max_iters):
    """Hill climb on voltages and endpoints; return the edge list when the diameter holds."""
    n = 2 * k * G
    Bs = [j for j in range(k) for _ in range(d)]
    rng.shuffle(Bs)
    darts = [[i, Bs[i * d + t], rng.randrange(G)] for i in range(k) for t in range(d)]

    def evaluate():
        edges = _lift(k, G, mul, darts)
        adj = [[] for _ in range(n)]
        for a, b in edges:
            adj[a].append(b)
            adj[b].append(a)
        return _bad(n, adj, D), edges

    cur, edges = evaluate()
    it = 0
    while cur > 0 and it < max_iters and time.monotonic() < deadline:
        it += 1
        if rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(G)
            new, e2 = evaluate()
            if new <= cur:
                cur, edges = new, e2
            else:
                darts[idx][2] = old
        else:
            i1 = rng.randrange(len(darts))
            i2 = rng.randrange(len(darts))
            if i1 == i2 or darts[i1][1] == darts[i2][1]:
                continue
            darts[i1][1], darts[i2][1] = darts[i2][1], darts[i1][1]
            new, e2 = evaluate()
            if new <= cur:
                cur, edges = new, e2
            else:
                darts[i1][1], darts[i2][1] = darts[i2][1], darts[i1][1]
    return edges if cur == 0 else None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        moore = lib.moore_bound(d, D)

        # Structured bases: projective plane (D = 3) or quadrangle W(q) (D = 4).
        if D == 3:
            q = _largest_pp(d - 1)
            if q is not None:
                consider(*lib.projective_plane_incidence(q))
        elif D == 4:
            q = _largest_pp(min(d - 1, 8))
            if q is not None:
                consider(*_gq_w(q))

        if best[0] >= moore:
            return best

        # Hill-climbing lift search for orders above the current best.
        target = best[0] + 1
        slice_len = max(1.0, budget / 10.0)
        while time.monotonic() < deadline and target <= moore:
            k = rng.randint(2, 6)
            G = max(2, -(-target // (2 * k)))
            if 2 * k * G > moore:
                continue
            mul = _random_mul(G, rng)
            slice_dl = min(deadline, time.monotonic() + slice_len)
            edges = _climb(k, G, mul, d, D, rng, slice_dl, 3000)
            if edges is not None:
                n = 2 * k * G
                if lib.is_valid(n, edges, d, D) and n > best[0]:
                    best = (n, edges)
                    target = n + 1
    except Exception:
        pass

    return best
