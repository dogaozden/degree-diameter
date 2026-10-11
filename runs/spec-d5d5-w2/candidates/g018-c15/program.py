import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# New construction: voltage lifts of generalized-polygon / projective-plane
# incidence graphs over small (possibly non-abelian) groups.
#
# Base graphs (both d-regular and bipartite when q = d - 1 is a prime power):
#   * PG(2, q) incidence: diameter 3, 2(q^2+q+1) vertices.
#   * W(q) generalized-quadrangle incidence: diameter 4, 2(q+1)(q^2+1) vertices.
# A G-lift replaces each base vertex by G copies (x in group G) and each base
# edge (a, b, s) by the matching (a, x) ~ (b, x*s). Degrees are preserved, the
# lift is simple and bipartite, and left translation is an automorphism, so
# diameter <= D only needs checking from the identity copy of each base vertex.
# Voltages are searched by simulated annealing with a bitmask ball-growth cost.
# Every candidate passes lib.is_valid before it is kept, and the fallback is
# always K_{d,d} (or the valid base graph itself).
# ----------------------------------------------------------------------------

RESTART_ITERS = 1500   # annealing steps per random restart
MAX_G = 12             # largest lift order tried
ATTEMPT_CAP = 15.0     # seconds cap for a single (base, G) attempt


def _proj_points(q, dim):
    """Normalized projective points of GF(q)^dim (first nonzero coordinate is 1)."""
    return [v for v in itertools.product(range(q), repeat=dim)
            if any(v) and next(c for c in v if c) == 1]


def _pg_base(q):
    """PG(2, q) incidence graph as (n, edges): points 0..m-1, lines m..2m-1."""
    n2, e = lib.projective_plane_incidence(q)
    bedges = [(min(u, v), max(u, v)) for u, v in e]
    return n2, bedges


def _gq_base(q):
    """Incidence graph of the generalized quadrangle W(q) as (n, edges), or None."""
    F = lib.GF(q)
    pts = _proj_points(q, 4)
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = F.inv(c)
        return tuple(F.mul(ic, x) for x in v)

    def form(x, y):
        # Symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2 over GF(q).
        return F.add(F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0])),
                     F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

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

    if len(lines) != P:
        return None
    nb = 2 * P
    bedges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    deg = [0] * nb
    for a, b in bedges:
        deg[a] += 1
        deg[b] += 1
    if any(x != q + 1 for x in deg):
        return None
    return nb, bedges


def _groups_for(G):
    """MUL tables (MUL[x][s] = x*s, identity coded 0) for cyclic and semidirect groups of order G."""
    out = []
    _, mul, _ = lib.cyclic_group(G)
    out.append([[mul(x, s) for s in range(G)] for x in range(G)])
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                try:
                    _, mul, _ = lib.semidirect_group(m, k, r)
                except ValueError:
                    continue
                out.append([[mul(x, s) for s in range(G)] for x in range(G)])
    return out


def _tree_mask(nb, bedges):
    """Spanning-forest marks on base edges. Tree voltages can be fixed to the identity WLOG."""
    adj = [[] for _ in range(nb)]
    for i, (a, b) in enumerate(bedges):
        adj[a].append((b, i))
        adj[b].append((a, i))
    tree = [False] * len(bedges)
    seen = [False] * nb
    for root in range(nb):
        if seen[root]:
            continue
        seen[root] = True
        stack = [root]
        while stack:
            u = stack.pop()
            for v, i in adj[u]:
                if not seen[v]:
                    seen[v] = True
                    tree[i] = True
                    stack.append(v)
    return tree


def _cost(N, E, nb, G, D):
    """Number of (base representative, vertex) pairs not within distance D. Zero iff valid."""
    adj = [[] for _ in range(N)]
    for u, w in E:
        adj[u].append(w)
        adj[w].append(u)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - reach[p * G].bit_count() for p in range(nb))


def _anneal(nb, bedges, tree, G, D, groups, rng, deadline):
    """Anneal voltages of a G-lift of the base graph; return the lift edge list or None."""
    N = nb * G
    m = len(bedges)
    free = [i for i in range(m) if not tree[i]]
    if not free:
        return None
    while time.monotonic() < deadline:
        MUL = rng.choice(groups)
        volt = [0] * m
        for i in free:
            volt[i] = rng.randrange(G)
        E = [None] * (m * G)

        def set_edge(i, s):
            a, b = bedges[i]
            ba = a * G
            bb = b * G
            for x in range(G):
                E[i * G + x] = (ba + x, bb + MUL[x][s])

        for i in range(m):
            set_edge(i, volt[i])
        cur = _cost(N, E, nb, G, D)
        for it in range(RESTART_ITERS):
            if cur == 0:
                return E
            if time.monotonic() > deadline:
                return None
            i = rng.choice(free)
            old = volt[i]
            new = rng.randrange(G - 1)
            if new >= old:
                new += 1
            set_edge(i, new)
            c2 = _cost(N, E, nb, G, D)
            delta = c2 - cur
            T = 1.0 * (1.0 - it / RESTART_ITERS) + 0.05
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                volt[i] = new
                cur = c2
            else:
                set_edge(i, old)
        if cur == 0:
            return E
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 6.0))
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

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Base graphs: incidence graphs of PG(2,q) and W(q) with q = d-1.
    q = d - 1
    bases = []
    if q >= 2 and lib.is_prime_power(q):
        cand_bases = [_pg_base(q)]
        if D >= 4:
            gq = _gq_base(q)
            if gq is not None:
                cand_bases.append(gq)
        for nb, bedges in cand_bases:
            consider(nb, bedges)
            bases.append((nb, bedges, _tree_mask(nb, bedges)))

    # Lift search: repeatedly attempt the smallest lift that beats the current best.
    failed = set()
    groups_cache = {}
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0:
            break
        cands = []
        for bi, (nb, _, _) in enumerate(bases):
            for G in range(2, MAX_G + 1):
                size = nb * G
                if best[0] < size <= moore and (bi, G) not in failed:
                    cands.append((size, bi, G))
        if not cands:
            break
        _, bi, G = min(cands)
        if G not in groups_cache:
            groups_cache[G] = _groups_for(G)
        nb, bedges, tree = bases[bi]
        slice_len = max(2.0, min(0.5 * remaining, ATTEMPT_CAP))
        end = min(deadline, now + slice_len)
        res = _anneal(nb, bedges, tree, G, D, groups_cache[G], rng, end)
        failed.add((bi, G))
        if res is not None:
            consider(nb * G, res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
