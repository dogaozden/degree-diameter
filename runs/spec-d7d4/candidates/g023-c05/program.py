import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallback bases: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

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


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _wq_best(d):
    """Incidence graph of W(q) for the largest prime power q with q + 1 <= d (capped for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group lifts: a bipartite base with a vertices per side, each vertex of degree d,
# darts (u, v, g) with g in a finite group G of order M. Lift vertices (block, x),
# edge (u, x) -- (a+v, x*g). Left multiplication by G is an automorphism that is
# transitive on each block, so diameter <= D is checked by BFS from the 2a block
# identities only. Cost = number of (source, vertex) pairs at distance > D.
# ----------------------------------------------------------------------------

def _make_group(M, rng):
    """Random group of order M (non-cyclic semidirect product when possible); return (MT, INV)."""
    opts = []
    for m in range(2, M):
        if M % m == 0 and M // m >= 2:
            k = M // m
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    opts.append((m, k, r))
    if opts and rng.random() < 0.7:
        m, k, r = rng.choice(opts)
        _, mul, inv = lib.semidirect_group(m, k, r)
    else:
        _, mul, inv = lib.cyclic_group(M)
    MT = [[mul(x, y) for y in range(M)] for x in range(M)]
    INV = [inv(x) for x in range(M)]
    return MT, INV


def _cost(a, D, M, MT, INV, darts):
    """Sum over the 2a block identities of the number of vertices at distance > D."""
    N = 2 * a * M
    Aadj = [[] for _ in range(a)]
    Badj = [[] for _ in range(a)]
    for u, v, g in darts:
        Aadj[u].append(((a + v) * M, g))
        Badj[v].append((u * M, INV[g]))
    total = 0
    for s in range(2 * a):
        seen = bytearray(N)
        start = s * M
        seen[start] = 1
        frontier = [start]
        cnt = 1
        for _ in range(D):
            nf = []
            for idx in frontier:
                b, x = divmod(idx, M)
                row = MT[x]
                if b < a:
                    for off, g in Aadj[b]:
                        j = off + row[g]
                        if not seen[j]:
                            seen[j] = 1
                            nf.append(j)
                else:
                    for off, gi in Badj[b - a]:
                        j = off + row[gi]
                        if not seen[j]:
                            seen[j] = 1
                            nf.append(j)
            if not nf:
                break
            cnt += len(nf)
            frontier = nf
        total += N - cnt
    return total


def _search(a, d, D, M, MT, INV, rng, deadline):
    """Anneal voltages on a fixed base until the lift has diameter <= D; return (N, edges) or None."""
    N = 2 * a * M
    vs = [i % a for i in range(d * a)]
    rng.shuffle(vs)
    darts = []
    keys = set()
    for idx in range(d * a):
        u = idx // d
        v = vs[idx]
        g = rng.randrange(M)
        while (u, v, g) in keys:
            g = rng.randrange(M)
        keys.add((u, v, g))
        darts.append([u, v, g])

    cur = _cost(a, D, M, MT, INV, darts)
    T = 0.8
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        if rng.random() < 0.5:
            # Change the voltage of one dart.
            k = rng.randrange(len(darts))
            u, v, g = darts[k]
            ng = rng.randrange(M)
            if ng == g or (u, v, ng) in keys:
                continue
            keys.discard((u, v, g))
            keys.add((u, v, ng))
            darts[k][2] = ng
            new = _cost(a, D, M, MT, INV, darts)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                keys.discard((u, v, ng))
                keys.add((u, v, g))
                darts[k][2] = g
        else:
            # Swap the B-endpoints of two darts (keeps all base degrees).
            k1 = rng.randrange(len(darts))
            k2 = rng.randrange(len(darts))
            u1, v1, g1 = darts[k1]
            u2, v2, g2 = darts[k2]
            if v1 == v2:
                continue
            n1 = (u1, v2, g1)
            n2 = (u2, v1, g2)
            if n1 in keys or n2 in keys:
                continue
            keys.discard((u1, v1, g1))
            keys.discard((u2, v2, g2))
            keys.add(n1)
            keys.add(n2)
            darts[k1][1] = v2
            darts[k2][1] = v1
            new = _cost(a, D, M, MT, INV, darts)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                keys.discard(n1)
                keys.discard(n2)
                keys.add((u1, v1, g1))
                keys.add((u2, v2, g2))
                darts[k1][1] = v1
                darts[k2][1] = v2

    edges = []
    for u, v, g in darts:
        for x in range(M):
            edges.append((u * M + x, (a + v) * M + MT[x][g]))
    if lib.is_valid(N, edges, d, D):
        return N, edges
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.5)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}, optimal for D = 2
    if d == 2:
        n = 2 * D  # even cycle: bipartite, max degree 2, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}.
    best = lib.haar_graph(d, range(d))

    def consider(res):
        nonlocal best
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    if D == 3:
        consider(_pg_best(d))
    elif D >= 4:
        consider(_wq_best(d))

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    rng = random.Random(seed)

    # Lift search: try increasing even orders above the current best.
    target = best[0] + 2
    while time.monotonic() < deadline and target <= moore:
        opts = [a for a in range(1, 7)
                if target % (2 * a) == 0 and target // (2 * a) >= d]
        if not opts:
            target += 2
            continue
        a = rng.choice(opts)
        M = target // (2 * a)
        now = time.monotonic()
        slice_end = min(deadline, now + 2.5)
        MT, INV = _make_group(M, rng)
        res = _search(a, d, D, M, MT, INV, rng, slice_end)
        if res is not None:
            consider(res)
            target = best[0] + 2
        else:
            target += 2

    return best
