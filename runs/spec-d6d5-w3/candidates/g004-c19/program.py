import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs.
#   * W(q): incidence graph of the generalized quadrangle W(q). It is (q+1)-regular
#     with diameter 4 and 2(q+1)(q^2+1) vertices. For d = 6 it is W(5) with 312 vertices.
#   * bi-Cayley: k points and k lines per layer, d random permutation layers.
# Every candidate is a Z_m voltage lift (regular cover) of one of these bases.
# Left translation by the group is an automorphism of the lift, so the lift has
# diameter <= D iff the ball of each fibre representative (u, identity) covers everything.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and totally isotropic lines of W(q). Returns (n, edges)."""
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
    edges = []
    nl = 0
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
            for p in L:
                edges.append((p, P + nl))
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nl += 1
    return 2 * P, edges


def _bicayley_base(d, k, rng):
    """Base with k A-vertices and k B-vertices; each of d layers is a random permutation."""
    uv = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            uv.append((i, k + p[i]))
    return 2 * k, uv


# ----------------------------------------------------------------------------
# Group tables and voltage lifts.
# ----------------------------------------------------------------------------

def _table(G, mul):
    """T[s][x] = x * s in the group (right multiplication by s)."""
    return [[mul(x, s) for x in range(G)] for s in range(G)]


def _random_group(G, rng):
    """Random group of order G: a semidirect product Z_m x| Z_k2 when possible, else cyclic."""
    if rng.random() < 0.5:
        options = []
        for k2 in (2, 3, 4, 5, 6):
            if G % k2:
                continue
            m = G // k2
            if m < 2:
                continue
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if cands:
                options.append((m, k2, cands))
        if options:
            m, k2, cands = rng.choice(options)
            order, mul, _ = lib.semidirect_group(m, k2, rng.choice(cands))
            return order, mul
    order, mul, _ = lib.cyclic_group(G)
    return order, mul


def _cost(nb, uv, s, m, T, D):
    """Number of (fibre representative, vertex) pairs at distance > D. Zero iff the lift is valid."""
    N = nb * m
    adj = [[] for _ in range(N)]
    for (u, v), sv in zip(uv, s):
        row = T[sv]
        ub = u * m
        vb = v * m
        for x in range(m):
            a = ub + x
            b = vb + row[x]
            adj[a].append(b)
            adj[b].append(a)
    ball = [1 << i for i in range(N)]
    for _ in range(D):
        nxt = [0] * N
        for i in range(N):
            acc = ball[i]
            for j in adj[i]:
                acc |= ball[j]
            nxt[i] = acc
        ball = nxt
    total = 0
    for u in range(nb):
        total += N - ball[u * m].bit_count()
    return total


def _lift_edges(nb, uv, s, m, T):
    """Edge list of the lift, deduplicated."""
    E = set()
    for (u, v), sv in zip(uv, s):
        row = T[sv]
        for x in range(m):
            a = u * m + x
            b = v * m + row[x]
            E.add((a, b) if a < b else (b, a))
    return nb * m, sorted(E)


def _search(nb, uv, m, T, D, rng, deadline, cap):
    """Annealed search over voltages with restarts. Returns (best_cost, best_voltages)."""
    E = len(uv)
    best_cost, best_s = None, None
    while time.monotonic() < deadline:
        s = [rng.randrange(m) for _ in range(E)]
        cost = _cost(nb, uv, s, m, T, D)
        temp = 4.0
        for _ in range(cap):
            if cost == 0 or time.monotonic() >= deadline:
                break
            i = rng.randrange(E)
            old = s[i]
            new = rng.randrange(m)
            if new == old:
                continue
            s[i] = new
            c2 = _cost(nb, uv, s, m, T, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                s[i] = old
            temp = max(0.3, temp * 0.998)
        if best_cost is None or cost < best_cost:
            best_cost, best_s = cost, list(s)
        if cost == 0:
            break
    return best_cost, best_s


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    q = d - 1
    has_pg = q >= 2 and lib.is_prime_power(q)
    if D >= 3 and has_pg:
        consider(*lib.projective_plane_incidence(q))
    if D >= 4 and has_pg:
        consider(*_gq_w(q))

    # Shortcut: already at the Moore bound.
    if best_n >= lib.moore_bound(d, D):
        return best

    try:
        # Stage 1: voltage lifts of W(q) (diameter 4, degree d), so diameter 5 is the goal.
        if D >= 4 and has_pg:
            nbW, edgesW = _gq_w(q)
            uvW = list(edgesW)
            for m, frac in ((2, 0.3), (3, 0.5)):
                remaining = max(0.0, end - time.monotonic())
                t_end = time.monotonic() + frac * remaining
                _, mul, _ = lib.cyclic_group(m)
                T = _table(m, mul)
                cost, s = _search(nbW, uvW, m, T, D, rng, t_end, cap=3000)
                if cost == 0 and s is not None:
                    n, e = _lift_edges(nbW, uvW, s, m, T)
                    consider(n, e)
                if best_n >= lib.moore_bound(d, D):
                    return best

        # Stage 2: bi-Cayley voltage lifts over random groups, until time runs out.
        while time.monotonic() < end and best_n < lib.moore_bound(d, D):
            k = rng.choice([2, 3])
            lo = max(2, 640 // (2 * k))
            hi = max(lo, 1000 // (2 * k))
            G = rng.randint(lo, hi)
            order, mul = _random_group(G, rng)
            T = _table(order, mul)
            nb, uv = _bicayley_base(d, k, rng)
            t_end = min(end, time.monotonic() + 10.0)
            cost, s = _search(nb, uv, order, T, D, rng, t_end, cap=2000)
            if cost == 0 and s is not None:
                n, e = _lift_edges(nb, uv, s, order, T)
                consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
