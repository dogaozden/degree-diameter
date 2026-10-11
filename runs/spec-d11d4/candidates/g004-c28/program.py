import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane and generalized quadrangle incidence graphs.
# Points occupy indices 0..P-1 (side 0) and lines P..2P-1 (side 1).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW IDEA: degree-preserving "edge-split double insertion".
#
# Take a matching of d edges (x_i, y_i) (x side 0, y side 1) and delete them.
# Add two new vertices a (side 0) and b (side 1), with a ~ y_i and b ~ x_i.
# Every old vertex keeps its degree, and a, b get degree d. So the whole graph
# stays d-regular (on the saturated part) and bipartite, and +2 vertices are
# added at once without needing any spare degree. The diameter can break, so
# random 2-switches (x1,y1),(x2,y2) -> (x1,y2),(x2,y1) repair it. A switch
# keeps all degrees and bipartiteness. The insertion is kept only if the
# number of bad pairs reaches 0; otherwise it is discarded.
# ----------------------------------------------------------------------------

def _adj_from(n, E):
    adj = [[] for _ in range(n)]
    for x, y in E:
        adj[x].append(y)
        adj[y].append(x)
    return adj


def _count_bad(n, adj, D):
    """Number of unordered pairs at distance > D, via radius-D bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _saturate(n, side, E, d, rng):
    """Add edges between deficient opposite-side vertices, avoiding duplicates."""
    E = list(E)
    deg = [0] * n
    ex = set()
    for x, y in E:
        deg[x] += 1
        deg[y] += 1
        ex.add((x, y))
    L = [v for v in range(n) if side[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if side[v] == 1 and deg[v] < d]
    tries = 0
    while L and R and tries < 400000:
        tries += 1
        a = rng.choice(L)
        b = rng.choice(R)
        if (a, b) in ex:
            continue
        E.append((a, b))
        ex.add((a, b))
        deg[a] += 1
        deg[b] += 1
        if deg[a] >= d:
            L.remove(a)
        if deg[b] >= d:
            R.remove(b)
    return E


def _repair(N, E, adj, D, rng, deadline, max_sweeps):
    """Random 2-switches on E (in place, adj kept in sync). True if no bad pairs remain."""
    Eset = set(E)
    bad = _count_bad(N, adj, D)
    sweeps = 0
    m = len(E)
    while bad > 0 and sweeps < max_sweeps and time.monotonic() < deadline:
        sweeps += 1
        i, j = rng.sample(range(m), 2)
        x1, y1 = E[i]
        x2, y2 = E[j]
        if x1 == x2 or y1 == y2:
            continue
        a = (x1, y2)
        b = (x2, y1)
        if a in Eset or b in Eset:
            continue
        adj[x1].remove(y1); adj[y1].remove(x1)
        adj[x2].remove(y2); adj[y2].remove(x2)
        adj[x1].append(y2); adj[y2].append(x1)
        adj[x2].append(y1); adj[y1].append(x2)
        nb = _count_bad(N, adj, D)
        if nb <= bad:
            bad = nb
            E[i] = a
            E[j] = b
            Eset.discard((x1, y1))
            Eset.discard((x2, y2))
            Eset.add(a)
            Eset.add(b)
        else:
            adj[x1].remove(y2); adj[y2].remove(x1)
            adj[x2].remove(y1); adj[y1].remove(x2)
            adj[x1].append(y1); adj[y1].append(x1)
            adj[x2].append(y2); adj[y2].append(x2)
    return bad == 0


def _split_insert(n, E, d, D, rng, deadline, max_sweeps):
    """One edge-split double insertion plus repair. Returns (N, E2) on success, else None."""
    m = len(E)
    idx = list(range(m))
    rng.shuffle(idx)
    usedx, usedy, chosen = set(), set(), []
    for i in idx:
        x, y = E[i]
        if x in usedx or y in usedy:
            continue
        usedx.add(x)
        usedy.add(y)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    cs = set(chosen)
    R = [E[i] for i in chosen]
    E2 = [E[i] for i in range(m) if i not in cs]
    a, b, N = n, n + 1, n + 2
    for x, y in R:
        E2.append((a, y))   # a (side 0) ~ y (side 1)
        E2.append((x, b))   # x (side 0) ~ b (side 1)
    adj = _adj_from(N, E2)
    if _repair(N, E2, adj, D, rng, deadline, max_sweeps):
        return N, E2
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    base = None
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            base = gq
    if base is None:
        base = _best_pg(d)
    if base is None:
        return best

    bn, be = base
    half = bn // 2
    side = [0] * half + [1] * (bn - half)
    E = _saturate(bn, side, be, d, rng)
    n = bn
    consider(n, E)

    bound = lib._moore_bound(d, D)
    while time.monotonic() < deadline and n + 2 <= bound:
        res = _split_insert(n, E, d, D, rng, deadline, 150)
        if res is None:
            continue
        n, E = res
        side = side + [0, 1]

    if n > best_n:
        consider(n, E)
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
