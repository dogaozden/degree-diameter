import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points and lines of the symplectic quadrangle,
# incidence graph has 2(q+1)(q^2+1) vertices, is (q+1)-regular, diameter 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
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


def _adj_lists(n, edges):
    nbr = [[] for _ in range(n)]
    for u, v in edges:
        nbr[u].append(v)
        nbr[v].append(u)
    return nbr


# ----------------------------------------------------------------------------
# Deletion-based construction from a base graph of degree q+1 > d.
# Choose an alive set S of base vertices such that
#   (a) every alive vertex has at least k = q+1-d dead neighbours (degree <= d),
#   (b) the induced subgraph on S has diameter <= D.
# Cost = 3 * (#undominated alive vertices) + (#pairs at distance > D in S).
# Simulated annealing at fixed |S|; the size is climbed upward while feasible.
# ----------------------------------------------------------------------------

def _evaluate(alive, nbr, N, k, D):
    undom = []
    for v in range(N):
        if alive[v]:
            dead = 0
            for u in nbr[v]:
                if not alive[u]:
                    dead += 1
            if dead < k:
                undom.append(v)
    S = [v for v in range(N) if alive[v]]
    A = len(S)
    if A == 0:
        return 10 ** 9, undom, 0
    idx = [-1] * N
    for i, v in enumerate(S):
        idx[v] = i
    adjS = [[idx[u] for u in nbr[v] if alive[u]] for v in S]
    reach = [1 << i for i in range(A)]
    for _ in range(D):
        new = []
        for i in range(A):
            r = reach[i]
            for j in adjS[i]:
                r |= reach[j]
            new.append(r)
        reach = new
    bad = sum(A - r.bit_count() for r in reach) // 2
    return 3 * len(undom) + bad, undom, bad


def _anneal(alive, nbr, N, k, D, iters, rng, deadline):
    cost, undom, _ = _evaluate(alive, nbr, N, k, D)
    if cost == 0:
        return True
    T0 = 1.5
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (0.01 ** (it / max(1, iters)))
        S = [v for v in range(N) if alive[v]]
        Dd = [v for v in range(N) if not alive[v]]
        if not S or not Dd:
            break
        if undom and rng.random() < 0.5:
            u = rng.choice(undom)
            cands = [w for w in nbr[u] if alive[w]]
            if not cands:
                continue
            w = rng.choice(cands)
            z = rng.choice(Dd)
            changes = [(w, False), (z, True)]
        else:
            x = rng.choice(S)
            z = rng.choice(Dd)
            changes = [(x, False), (z, True)]
        for v, s in changes:
            alive[v] = s
        new_cost, new_undom, _ = _evaluate(alive, nbr, N, k, D)
        if new_cost <= cost or rng.random() < math.exp(-(new_cost - cost) / T):
            cost, undom = new_cost, new_undom
        else:
            for v, s in changes:
                alive[v] = not s
    return cost == 0


def _resize(alive, A, nbr, N, k, D, rng):
    cur = sum(alive)
    while cur < A:
        Dd = [v for v in range(N) if not alive[v]]
        best = None
        for z in rng.sample(Dd, min(6, len(Dd))):
            alive[z] = True
            c = _evaluate(alive, nbr, N, k, D)[0]
            alive[z] = False
            if best is None or c < best[0]:
                best = (c, z)
        alive[best[1]] = True
        cur += 1
    while cur > A:
        Sl = [v for v in range(N) if alive[v]]
        best = None
        for x in rng.sample(Sl, min(6, len(Sl))):
            alive[x] = False
            c = _evaluate(alive, nbr, N, k, D)[0]
            alive[x] = True
            if best is None or c < best[0]:
                best = (c, x)
        alive[best[1]] = False
        cur -= 1
    return alive


def _induced(N, edges, alive):
    idx = [-1] * N
    c = 0
    for v in range(N):
        if alive[v]:
            idx[v] = c
            c += 1
    E = [(idx[u], idx[v]) for u, v in edges if alive[u] and alive[v]]
    return c, E


def _deletion_search(d, D, deadline, rng):
    q = None
    for cand in range(max(2, d - 1), 10):
        if lib.is_prime_power(cand):
            q = cand
            break
    if q is None:
        return None
    k = q + 1 - d
    N, edges = _gq_w(q)
    if k <= 0:
        # Base graph already has max degree d (q + 1 == d); diameter 4 holds.
        return N, edges
    nbr = _adj_lists(N, edges)

    A = max(2, int(0.3 * N))
    alive = [False] * N
    for v in rng.sample(range(N), A):
        alive[v] = True
    best = None
    step = 8
    iters = 1200
    while time.monotonic() < deadline:
        alive = _resize(alive, A, nbr, N, k, D, rng)
        ok = _anneal(alive, nbr, N, k, D, iters, rng, deadline)
        if ok:
            best = (A, list(alive))
            A = min(N - 1, A + step)
        else:
            if best is None:
                A -= 16
                if A <= 1:
                    break
            else:
                alive = list(best[1])
                if step > 1:
                    step //= 2
                A = best[0] + step
    if best is None:
        return None
    return _induced(N, edges, best[1])


# ----------------------------------------------------------------------------
# Driver.
# D = 3: projective plane incidence graph of the largest prime power q with q+1 <= d.
# D = 4: deletion search on W(q); fallback K_{d,d} (diameter 2, valid for D >= 2).
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D == 3:
            qs = [q for q in range(2, d) if lib.is_prime_power(q)]
            if qs:
                n, e = lib.projective_plane_incidence(max(qs))
                consider(n, e)
        elif D == 4:
            res = _deletion_search(d, D, deadline, rng)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
