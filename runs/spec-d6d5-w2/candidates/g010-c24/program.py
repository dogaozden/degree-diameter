import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------

def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Points and lines of the generalized quadrangle W(q) (totally isotropic lines of a
    symplectic form on GF(q)^4).

    Returns (n0, edges, side) for the incidence graph: points are 0..P-1 (side 0),
    lines are P..P+L-1 (side 1). Returns None if the structure is not as expected.
    """
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
            if len(L) != q + 1:
                return None
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    side = [0] * P + [1] * len(lines)
    return P + len(lines), edges, side


def _reach(n, adj, D):
    """Bitmask per vertex of the ball of radius D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _total(N, E, D):
    """Number of ordered (vertex, vertex) pairs at distance > D (including unreachable)."""
    adj = [[] for _ in range(N)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    reach = _reach(N, adj, D)
    return sum(N - r.bit_count() for r in reach)


def _saturate(n, edges, side, d, rng):
    """Add edges between deficient opposite-side vertices. Never breaks degree or diameter."""
    deg = [0] * n
    ex = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        ex.add((min(u, v), max(u, v)))
    L = [v for v in range(n) if side[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if side[v] == 1 and deg[v] < d]
    cand = [(a, b) for a in L for b in R if (min(a, b), max(a, b)) not in ex]
    rng.shuffle(cand)
    out = list(edges)
    for a, b in cand:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return out


def _compact(n, edges, side, keep):
    new = [-1] * n
    cnt = 0
    side2 = []
    for v in range(n):
        if keep[v]:
            new[v] = cnt
            cnt += 1
            side2.append(side[v])
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return cnt, E, side2


# ----------------------------------------------------------------------------
# Z_m voltage lifts of the W(q) incidence graph, annealed on the bad-pair count.
# ----------------------------------------------------------------------------

def _lift_edges(n0, m, base, volt):
    E = []
    for (u, v), a in zip(base, volt):
        for g in range(m):
            E.append((u * m + g, v * m + (g + a) % m))
    return n0 * m, E


def _anneal(n0, m, base, D, until, rng):
    """Anneal voltages until the lift has diameter <= D or time runs out.

    Returns (best_cost, best_volt).
    """
    E0 = len(base)
    t0 = time.monotonic()
    span = max(1e-3, until - t0)
    volt = [rng.randrange(m) for _ in range(E0)]
    N, E = _lift_edges(n0, m, base, volt)
    cost = _total(N, E, D)
    best_cost, best_volt = cost, list(volt)
    while cost > 0:
        now = time.monotonic()
        if now >= until:
            break
        frac = (now - t0) / span
        T = 4.0 * (0.125 ** frac)
        i = rng.randrange(E0)
        old = volt[i]
        new = rng.randrange(m)
        if new == old:
            continue
        volt[i] = new
        N, E = _lift_edges(n0, m, base, volt)
        c2 = _total(N, E, D)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            cost = c2
            if cost < best_cost:
                best_cost, best_volt = cost, list(volt)
        else:
            volt[i] = old
    return best_cost, best_volt


def _repair(n, edges, side, d, D, best_n, deadline, rng):
    """Delete the worst vertices in batches, saturating after each batch.

    Returns a valid (n, edges, side) with n > best_n, or None.
    """
    cur = (n, list(edges), list(side))
    while time.monotonic() < deadline:
        cn, cE, cS = cur
        if cn <= best_n:
            return None
        adj = [[] for _ in range(cn)]
        for u, v in cE:
            adj[u].append(v)
            adj[v].append(u)
        reach = _reach(cn, adj, D)
        bad = [cn - r.bit_count() for r in reach]
        if sum(bad) == 0:
            return cur
        order = sorted(range(cn), key=lambda v: (-bad[v], rng.random()))
        k = max(1, cn // 60)
        dead = set(order[:k])
        keep = [v not in dead for v in range(cn)]
        n2, E2, S2 = _compact(cn, cE, cS, keep)
        E2 = _saturate(n2, E2, S2, d, rng)
        cur = (n2, E2, S2)
    return None


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, bipartite, degree d.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    q = _largest_pp(d - 1)

    if D == 3:
        if q is not None:
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)
        return best

    # D >= 4: generalized quadrangle base W(q), diameter 4, degree q+1 <= d.
    if q is None or q > 7:
        return best
    gq = _gq_w(q)
    if gq is None:
        return best
    n0, base, side0 = gq
    consider(n0, base)
    if D == 4:
        return best

    # D >= 5: bold Z_m voltage-lift search over the W(q) base.
    T_eff = deadline - start
    states = []
    for m, frac in ((2, 0.2), (3, 0.65)):
        if time.monotonic() >= deadline:
            break
        until = start + frac * T_eff
        bc, bv = _anneal(n0, m, base, D, until, rng)
        if bc == 0:
            N, E = _lift_edges(n0, m, base, bv)
            consider(N, E)
        else:
            states.append((m, bv))

    # Repair the failed lifts by deletion (largest first), keeping only improvements.
    for m, bv in reversed(states):
        if time.monotonic() >= deadline:
            break
        N, E = _lift_edges(n0, m, base, bv)
        S = [side0[v // m] for v in range(N)]
        res = _repair(N, E, S, d, D, best_n, deadline, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
