import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases of degree q+1 <= d:
#   PG(2, q) (diameter 3) and the generalized quadrangle W(q) (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q), the symplectic quadrangle (diameter 4)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _bases(d):
    """Return (diameter, degree, order, edges) for regular bases of degree q+1 <= d."""
    out = []
    for q in range(d - 1, 1, -1):
        if q <= 23 and lib.is_prime_power(q):
            n, e = lib.projective_plane_incidence(q)
            out.append((3, q + 1, n, e))
            break
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            n, e = _gq_w(q)
            out.append((4, q + 1, n, e))
            break
    return out


# ----------------------------------------------------------------------------
# Bold route: Z_m voltage lifts of a base graph, annealed on voltages.
# An m-lift of a bipartite base stays bipartite and keeps the base degree.
# Voltages on a spanning tree can be fixed to 0 (switching), which shrinks
# the search space.
# ----------------------------------------------------------------------------

T_HI = 3.0
T_LO = 0.3
RUN_LEN = 4000


def _free_darts(nb, E):
    """Indices of base edges outside a fixed spanning tree (their voltages are free)."""
    adj = [[] for _ in range(nb)]
    for i, (u, v) in enumerate(E):
        adj[u].append((v, i))
        adj[v].append((u, i))
    seen = [False] * nb
    seen[0] = True
    tree = set()
    stack = [0]
    while stack:
        u = stack.pop()
        for v, i in adj[u]:
            if not seen[v]:
                seen[v] = True
                tree.add(i)
                stack.append(v)
    return [i for i in range(len(E)) if i not in tree]


def _lift_adj(nb, E, m, volt):
    """Adjacency lists of the Z_m lift: base edge (u, v) with voltage a joins u*m+g to v*m+(g+a)%m."""
    adj = [[] for _ in range(nb * m)]
    for (u, v), a in zip(E, volt):
        ub = u * m
        vb = v * m
        for g in range(m):
            x = ub + g
            y = vb + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    return adj


def _bad_pairs(N, adj, D):
    """Ordered count of vertex pairs at distance > D, via bitset balls."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _lift_edges(nb, E, m, volt):
    edges = []
    for (u, v), a in zip(E, volt):
        for g in range(m):
            edges.append((u * m + g, v * m + (g + a) % m))
    return nb * m, edges


def _anneal_lift(nb, E, m, free, D, rng, deadline):
    """Simulated annealing over lift voltages with restarts; returns voltages with zero bad pairs or None."""
    N = nb * m
    volt = [0] * len(E)
    if not free:
        return volt if _bad_pairs(N, _lift_adj(nb, E, m, volt), D) == 0 else None
    while time.monotonic() < deadline:
        for i in free:
            volt[i] = rng.randrange(m)
        cur = _bad_pairs(N, _lift_adj(nb, E, m, volt), D)
        for step in range(RUN_LEN):
            if cur == 0:
                return list(volt)
            if (step & 31) == 0 and time.monotonic() > deadline:
                return None
            temp = T_HI * (T_LO / T_HI) ** (step / RUN_LEN)
            i = free[rng.randrange(len(free))]
            old = volt[i]
            volt[i] = (old + 1 + rng.randrange(m - 1)) % m
            c2 = _bad_pairs(N, _lift_adj(nb, E, m, volt), D)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = c2
            else:
                volt[i] = old
        if cur == 0:
            return list(volt)
    return None


# ----------------------------------------------------------------------------
# Fallback route: Bi-Cayley graphs over Z_m x|_r Z_k, annealed connection sets.
# ----------------------------------------------------------------------------

CLIMB_ITERS = 800


def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(N, T, invs, S, D):
    """Unreached (source, target) pairs from A_0 and B_0; zero means D-diameter."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


def _bicayley(N, d, D, rng, deadline):
    """Try a few groups of order N; return the edge list of a valid Bi-Cayley graph, or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:6]:
        if time.monotonic() > deadline:
            break
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        invs = [inv(g) for g in range(order)]
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return [(x, N + T[x][g]) for x in range(N) for g in S]
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    bases = _bases(d)
    for db, _dg, nb, eb in bases:
        if db <= D:
            consider(nb, eb)

    # Lift phase: largest base with diameter below D, only if a lift can beat the base.
    usable = [b for b in bases if b[0] < D and 2 * b[2] > best[0]]
    lift_ok = False
    if usable:
        _db, _dg, nb, eb = max(usable, key=lambda b: b[2])
        E = list(eb)
        free = _free_darts(nb, E)
        volt = _anneal_lift(nb, E, 2, free, D, rng, start + 0.55 * budget)
        if volt is not None:
            consider(*_lift_edges(nb, E, 2, volt))
            lift_ok = True
            volt3 = _anneal_lift(nb, E, 3, free, D, rng, deadline)
            if volt3 is not None:
                consider(*_lift_edges(nb, E, 3, volt3))

    # Fallback search if the lift route did not succeed.
    if not lift_ok and d >= 2:
        moore = lib.moore_bound(d, D)
        while best[0] < moore and time.monotonic() < deadline:
            lo = best[0] // 2 + 1
            if lo > moore // 2:
                break
            window = max(2, lo // 10)
            N = min(moore // 2, lo + rng.randrange(window))
            if N < 2:
                break
            edges = _bicayley(N, d, D, rng, deadline)
            if edges is not None:
                consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
