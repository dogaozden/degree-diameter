import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
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


# ----------------------------------------------------------------------------
# Random d-regular bipartite graphs grown by vertex insertion and annealed by
# degree-preserving edge switches, minimising the number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad(N, nb, D):
    """Number of unordered vertex pairs at distance more than D (unreachable counts)."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = ball[v]
            for u in nb[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(N - b.bit_count() for b in ball) // 2


def _replace(lst, old, new):
    lst[lst.index(old)] = new


def _switch(nb, a, b, c, e):
    """Edges (a,b),(c,e) become (a,e),(c,b). Side-0 vertices a,c; side-1 vertices b,e."""
    _replace(nb[a], b, e)
    _replace(nb[b], a, c)
    _replace(nb[c], e, b)
    _replace(nb[e], c, a)


def _add_edge(nb, eset, E, a, b):
    nb[a].append(b)
    nb[b].append(a)
    eset.add((a, b))
    E.append((a, b))


def _grow(d, nb, col, E, eset, rng):
    """Insert one new side-0 vertex p and one new side-1 vertex q, keeping d-regularity.

    Pick d edges (a_i, b_i) with distinct endpoints; replace them by p-b_i and a_i-q.
    """
    idx = list(range(len(E)))
    rng.shuffle(idx)
    ua, ub, pick = set(), set(), []
    for i in idx:
        a, b = E[i]
        if a in ua or b in ub:
            continue
        ua.add(a)
        ub.add(b)
        pick.append(i)
        if len(pick) == d:
            break
    if len(pick) < d:
        return False
    pairs = [E[i] for i in pick]
    ps = set(pick)
    p = len(nb)
    nb.append([])
    col.append(0)
    q = len(nb)
    nb.append([])
    col.append(1)
    for a, b in pairs:
        nb[a].remove(b)
        nb[b].remove(a)
        eset.discard((a, b))
    E[:] = [E[i] for i in range(len(E)) if i not in ps]
    for a, b in pairs:
        _add_edge(nb, eset, E, a, q)
        _add_edge(nb, eset, E, p, b)
    return True


def _search(d, D, deadline, rng, consider):
    """Grow a d-regular bipartite graph from K_{d,d}; anneal to diameter <= D; keep growing on success."""
    col = [0] * d + [1] * d
    nb = [[] for _ in range(2 * d)]
    E, eset = [], set()
    for a in range(d):
        for b in range(d, 2 * d):
            _add_edge(nb, eset, E, a, b)
    if len(E) < 2:
        return

    cost = _bad(len(nb), nb, D)
    it = 0
    cyc = 2000
    while time.monotonic() < deadline:
        if cost == 0:
            consider(len(nb), [tuple(e) for e in E])
            if not _grow(d, nb, col, E, eset, rng):
                break
            cost = _bad(len(nb), nb, D)
            continue

        it += 1
        m = len(E)
        i, j = rng.sample(range(m), 2)
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in eset or (c, b) in eset:
            continue
        T = 1.2 * (0.05 ** ((it % cyc) / cyc))
        _switch(nb, a, b, c, e)
        new = _bad(len(nb), nb, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            _switch(nb, a, e, c, b)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.82 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured bases.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)][:1]
        for q in qs:
            if time.monotonic() < start + 0.2 * T:
                g_n, g_e = _gq_w(q)
                consider(g_n, g_e)

    # Already at the Moore bound: nothing to improve.
    if best[0] >= lib._moore_bound(d, D):
        return best

    # Main bold search: random regular bipartite growth with annealing.
    if d >= 2:
        _search(d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
