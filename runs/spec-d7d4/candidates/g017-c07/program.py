import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q): diameter 4, degree q+1."""
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
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nl += 1
    return P + nl, edges


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _exact_gq(d):
    """W(q) with q + 1 <= d (exact degree q+1), q the largest such prime power (q <= 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Deletion search: find a large induced subgraph of a big bipartite base graph
# with max degree <= d and diameter <= D. Vertices are toggled in and out.
# Cost = (bad pairs at distance > D inside the subgraph) + 4 * (degree excess).
# ----------------------------------------------------------------------------

def _evaluate(alive, N, adj, d, D):
    verts = [v for v in range(N) if alive[v]]
    S = len(verts)
    loc = [-1] * N
    for i, v in enumerate(verts):
        loc[v] = i
    an = []
    degviol = 0
    for v in verts:
        nb = [loc[u] for u in adj[v] if loc[u] >= 0]
        if len(nb) > d:
            degviol += len(nb) - d
        an.append(nb)
    reach = [1 << i for i in range(S)]
    for _ in range(D):
        new = []
        for i in range(S):
            r = reach[i]
            for j in an[i]:
                r |= reach[j]
            new.append(r)
        reach = new
    cnt = [r.bit_count() for r in reach]
    bad2 = sum(S - c for c in cnt)
    return bad2 // 2 + 4 * degviol, verts, cnt


def _boundary(alive, N, adj):
    out = set()
    for v in range(N):
        if alive[v]:
            for u in adj[v]:
                if not alive[u]:
                    out.add(u)
    return list(out)


def _rand_flag(alive, flag, rng, N):
    for _ in range(50 * N):
        v = rng.randrange(N)
        if alive[v] == flag:
            return v
    return None


def _search_base(N, E0, d, D, deadline, rng):
    adj = [[] for _ in range(N)]
    for u, v in E0:
        adj[u].append(v)
        adj[v].append(u)

    alive = [False] * N
    alive[rng.randrange(N)] = True
    best_alive, best_size = None, 0
    cost, verts, cnt = _evaluate(alive, N, adj, d, D)
    fails = 0

    while time.monotonic() < deadline:
        if cost == 0:
            if len(verts) > best_size:
                best_size = len(verts)
                best_alive = list(alive)
            bnd = _boundary(alive, N, adj)
            if not bnd:
                break
            rng.shuffle(bnd)
            bc = None
            for b in bnd[:6]:
                alive[b] = True
                c = _evaluate(alive, N, adj, d, D)[0]
                alive[b] = False
                if bc is None or c < bc[0]:
                    bc = (c, b)
                if time.monotonic() >= deadline:
                    break
            if bc is None:
                break
            alive[bc[1]] = True
            cost, verts, cnt = _evaluate(alive, N, adj, d, D)
            fails = 0
            continue

        bnd = _boundary(alive, N, adj)
        K = 200
        T0 = 4.0
        for it in range(K):
            if cost == 0 or time.monotonic() >= deadline:
                break
            T = T0 * (0.05 ** (it / K))
            a = _rand_flag(alive, True, rng, N)
            if bnd and rng.random() < 0.6:
                b = rng.choice(bnd)
            else:
                b = _rand_flag(alive, False, rng, N)
            if a is None or b is None or alive[b] or a == b:
                continue
            alive[a] = False
            alive[b] = True
            nc, nv, ncnt = _evaluate(alive, N, adj, d, D)
            delta = nc - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost, verts, cnt = nc, nv, ncnt
            else:
                alive[a] = True
                alive[b] = False

        if cost > 0:
            fails += 1
            if fails >= 3 and verts:
                worst = max(range(len(verts)), key=lambda i: len(verts) - cnt[i])
                alive[verts[worst]] = False
                cost, verts, cnt = _evaluate(alive, N, adj, d, D)
                fails = 0

    if cost == 0 and len(verts) > best_size:
        best_size = len(verts)
        best_alive = list(alive)
    if best_alive is None:
        return None
    ids = [v for v in range(N) if best_alive[v]]
    m = {v: i for i, v in enumerate(ids)}
    edges = [(m[u], m[v]) for u, v in E0 if best_alive[u] and best_alive[v]]
    return len(ids), edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if d == 2 and D >= 2:
        # Even cycle of length 2D has diameter D.
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D == 2:
        return best  # K_{d,d} is Moore-optimal here

    if D == 3:
        try:
            pg = _pg_best(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
        return best

    # D >= 4: generalized quadrangles.
    try:
        ex = _exact_gq(d)
        if ex is not None:
            consider(ex[0], ex[1])
    except Exception:
        pass

    if best[0] >= lib._moore_bound(d, D):
        return best

    # Bold route: take W(d) (degree d+1) and delete vertices until degrees fit in d.
    if 3 <= d <= 9 and lib.is_prime_power(d):
        try:
            bn, be = _gq_w(d)
            if lib.max_degree(bn, be) <= d:
                consider(bn, be)
            else:
                res = _search_base(bn, be, d, D, deadline, rng)
                if res is not None:
                    consider(res[0], res[1])
        except Exception:
            pass

    return best
