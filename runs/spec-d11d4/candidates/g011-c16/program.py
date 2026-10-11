import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points and totally isotropic lines.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

    def form(x, y):
        t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t][u]

    covered = bytearray(P * P)
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if covered[i * P + j]:
                continue
            y = pts[j]
            if form(x, y):
                continue
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered[p * P + r] = 1
    return P, lines


def _adjacency(P, lines):
    """Return (pl, padj, ladj): lines through each point, collinear points, and intersecting lines."""
    pl = [[] for _ in range(P)]
    padj = [set() for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
            padj[p].update(Ls)
    for p in range(P):
        padj[p].discard(p)
    ladj = [set() for _ in lines]
    for p in range(P):
        for a in pl[p]:
            ladj[a].update(pl[p])
    for a in range(len(lines)):
        ladj[a].discard(a)
    return pl, [sorted(s) for s in padj], [sorted(s) for s in ladj]


# ----------------------------------------------------------------------------
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n
    S = set()
    adjset = [set(a) for a in adj]

    def add(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.discard(u)
        for w in adj[u]:
            c[w] -= 1

    def local_search():
        while True:
            changed = False
            free = [v for v in range(n) if not inS[v] and c[v] == 0]
            rng.shuffle(free)
            for v in free:
                if not inS[v] and c[v] == 0:
                    add(v)
                    changed = True
            for x in list(S):
                if not inS[x]:
                    continue
                one = [u for u in adj[x] if c[u] == 1]
                if len(one) < 2:
                    continue
                rng.shuffle(one)
                pair = None
                for i in range(len(one)):
                    for j in range(i + 1, len(one)):
                        if one[j] not in adjset[one[i]]:
                            pair = (one[i], one[j])
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    remove(x)
                    add(pair[0])
                    add(pair[1])
                    changed = True
            if not changed:
                break

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and c[v] == 0:
            add(v)
    local_search()
    best = list(S)
    stale = 0

    while time.monotonic() < deadline:
        cand = [v for v in range(n) if not inS[v]]
        if not cand:
            break
        v = rng.choice(cand)
        for w in adj[v]:
            if inS[w]:
                remove(w)
        add(v)
        local_search()
        if len(S) > len(best):
            best = list(S)
            stale = 0
        else:
            stale += 1
        if len(S) < len(best) - 1 or stale > 300:
            for u in list(S):
                remove(u)
            for u in best:
                add(u)
            stale = 0
    return best


# ----------------------------------------------------------------------------
# Exact search for a full spread of W(q) (q^2+1 pairwise disjoint lines).
# Randomized DFS with the most-constrained-point heuristic and node caps.
# ----------------------------------------------------------------------------

def _exact_cover_once(P, lines, pl, until, rng, node_cap):
    """Try once to find a set of pairwise disjoint lines covering every point; return list or None."""
    alive = [True] * len(lines)
    covered = [False] * P
    chosen = []
    nodes = [0]

    def dfs():
        nodes[0] += 1
        if nodes[0] > node_cap or time.monotonic() > until:
            return False
        best_p, best_opts = -1, None
        for p in range(P):
            if covered[p]:
                continue
            opts = [j for j in pl[p] if alive[j]]
            if best_opts is None or len(opts) < len(best_opts):
                best_p, best_opts = p, opts
                if not opts:
                    return False
                if len(opts) == 1:
                    break
        if best_p < 0:
            return True
        rng.shuffle(best_opts)
        for j in best_opts:
            killed = []
            for p in lines[j]:
                covered[p] = True
                for k in pl[p]:
                    if alive[k]:
                        alive[k] = False
                        killed.append(k)
            chosen.append(j)
            if dfs():
                return True
            chosen.pop()
            for p in lines[j]:
                covered[p] = False
            for k in killed:
                alive[k] = True
            if nodes[0] > node_cap or time.monotonic() > until:
                return False
        return False

    if dfs():
        return list(chosen)
    return None


def _spread_restarts(P, lines, pl, until, rng):
    """Repeat randomized exact-cover attempts until the deadline; return a full spread or None."""
    while time.monotonic() < until:
        res = _exact_cover_once(P, lines, pl, until, rng, node_cap=400)
        if res is not None:
            return res
    return None


# ----------------------------------------------------------------------------
# Twin blow-up.
#
# Blowing up a base vertex v into two twins (same neighbourhood) is valid when
# every base vertex of degree d-1 has at most one blown-up neighbour. For W(q),
# the blown-up points must be pairwise non-collinear (a partial ovoid I) and the
# blown-up lines pairwise disjoint (a partial spread J). Points and lines never
# conflict with each other, so |I| and |J| are optimised separately.
# ----------------------------------------------------------------------------

def _blow_base(P, lines, I, J):
    """Blow up points in I and lines (by index) in J; return (n, edges)."""
    n = P + len(lines)
    pcopy = {}
    for p in I:
        pcopy[p] = n
        n += 1
    lcopy = {}
    for j in J:
        lcopy[P + j] = n
        n += 1
    edges = []
    for j, Ls in enumerate(lines):
        lv = P + j
        lvs = [lv] + ([lcopy[lv]] if lv in lcopy else [])
        for p in Ls:
            ps = [p] + ([pcopy[p]] if p in pcopy else [])
            for a in ps:
                for b in lvs:
                    edges.append((a, b))
    return n, edges


def _w_route(q, deadline, rng, blow):
    """Return (n, edges) for W(q) incidence, optionally blown up with a large partial ovoid and spread."""
    P, lines = _gq_w(q)
    L = len(lines)
    base_edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    if not blow:
        return P + L, base_edges

    pl, padj, ladj = _adjacency(P, lines)
    now = time.monotonic()
    span = max(0.0, deadline - now)
    spread = _spread_restarts(P, lines, pl, now + 0.25 * span, rng)
    if spread is not None and len(spread) == q * q + 1:
        J = spread
    else:
        J = _mis(L, ladj, now + 0.5 * span, rng)
    I = _mis(P, padj, deadline, rng)
    return _blow_base(P, lines, I, J)


def _generic_blowup(n0, e0, d, deadline, rng):
    """Blow up a (d-1)-regular base graph by a set with no two vertices at distance 2."""
    adj = [[] for _ in range(n0)]
    for u, v in e0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for x in a:
            for y in a:
                if x != y:
                    cs[x].add(y)
    nb = [sorted(s) for s in cs]
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    S = _mis(n0, nb, deadline, rng)
    extra = {}
    n = n0
    for v in S:
        extra[v] = n
        n += 1
    edges = []
    for u, v in e0:
        cu = [u] + ([extra[u]] if u in extra else [])
        cv = [v] + ([extra[v]] if v in extra else [])
        for a in cu:
            for b in cv:
                edges.append((a, b))
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.7 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D == 2:
        return best

    # Projective plane incidence: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Blow-up of PG(2, d-2) for D = 3 when PG(2, d-1) is unavailable.
    if D == 3 and lib.is_prime_power(d - 2) and d - 2 >= 2:
        try:
            n0, e0 = lib.projective_plane_incidence(d - 2)
            res = _generic_blowup(n0, e0, d, deadline, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_w_route(d - 1, deadline, rng, blow=False))
        except Exception:
            pass

    # W(d-2) with twin blow-up using the spare degree slot: degree d, diameter 4.
    q = d - 2
    if D >= 4 and 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline:
        try:
            consider(*_w_route(q, deadline, rng, blow=True))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
