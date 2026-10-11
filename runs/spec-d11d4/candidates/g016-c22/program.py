import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
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

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i * P + j) in covered:
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
                        covered.add(p * P + r)
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    inS = [False] * n
    c = [0] * n
    S = []

    def add(v):
        inS[v] = True
        S.append(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.remove(u)
        for w in adj[u]:
            c[w] -= 1

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if c[v] == 0:
            add(v)
    best = list(S)
    tab_add = [0] * n
    tab_rem = [0] * n
    it = 0
    stuck = 0
    while time.monotonic() < deadline:
        it += 1
        cost = sum(c[v] for v in S)
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                stuck = 0
            cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
                or [v for v in range(n) if not inS[v]]
            if not cands:
                break
            mn = min(c[v] for v in cands)
            add(rng.choice([v for v in cands if c[v] == mn]))
            continue
        stuck += 1
        if stuck > 3000:
            for v in list(S):
                remove(v)
            for v in best:
                add(v)
            stuck = 0
            continue
        ok = [u for u in S if tab_rem[u] <= it] or list(S)
        mx = max(c[u] for u in ok)
        u = rng.choice([x for x in ok if c[x] == mx])
        remove(u)
        tab_add[u] = it + rng.randint(5, 15)
        cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
            or [v for v in range(n) if not inS[v]]
        mn = min(c[v] for v in cands)
        v = rng.choice([x for x in cands if c[x] == mn])
        add(v)
        tab_rem[v] = it + rng.randint(5, 15)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    I = _mis(P, [sorted(s) for s in padj], mid, rng)
    J = _mis(L, [sorted(s) for s in ladj], deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------
# Spare-slot extension for diameter 4 with a set-cover rule.
#
# A new vertex x on side X joined to S (spare vertices on the opposite side
# from x) keeps diameter <= 4 when the union of R3(s), s in S, covers every
# live vertex. Adding vertices only shortens distances, so no other pair breaks.
#
# NEW IDEA (this version): perturb-and-regrow iterated local search with
# retirement. Extension vertices can be retired (their edges removed, their id
# recycled), which frees spare slots on their former neighbours. We then regrow
# greedily with those slots. A move is kept when the graph still has diameter
# <= 4 (checked exactly on the full live graph) and the vertex count does not
# drop. Otherwise the snapshot is restored. This is a plateau-walking search
# that can move between covers that a one-pass greedy can never reach.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _balls(n, adj, k):
    """Return per-vertex bitmasks of all vertices within distance k (ids may be dead: they have no edges)."""
    reach = [1 << v for v in range(n)]
    for _ in range(k):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _pick(pool, reach, unc, rng):
    """Choose the next cover vertex: best gain, or a random useful one with prob NOISE."""
    if rng.random() < NOISE:
        useful = [v for v in pool if reach[v] & unc]
        if useful:
            return rng.choice(useful)
        return -1
    best, bv = 0, -1
    for v in pool:
        g = (reach[v] & unc).bit_count()
        if g > best:
            best, bv = g, v
    return bv


def _state(n, edges):
    """Build the mutable extension state from a base graph, with a proper 2-colouring."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
    return {'adj': adj, 'color': color, 'alive': [True] * n, 'ext': [], 'free': []}


def _snap(st):
    return {'adj': [list(a) for a in st['adj']], 'color': list(st['color']),
            'alive': list(st['alive']), 'ext': list(st['ext']), 'free': list(st['free'])}


def _restore(st, snap):
    st['adj'] = [list(a) for a in snap['adj']]
    st['color'] = list(snap['color'])
    st['alive'] = list(snap['alive'])
    st['ext'] = list(snap['ext'])
    st['free'] = list(snap['free'])


def _remove(st, x):
    """Retire extension vertex x: drop its edges and recycle its id."""
    adj = st['adj']
    for w in adj[x]:
        adj[w].remove(x)
    adj[x] = []
    st['alive'][x] = False
    st['ext'].remove(x)
    st['free'].append(x)


def _grow_one(st, d, rng, attempts):
    """Try to add one extension vertex with a random spare seed; return True on success."""
    adj, color, alive = st['adj'], st['color'], st['alive']
    n = len(adj)
    reach = _balls(n, adj, 3)
    full = 0
    for v in range(n):
        if alive[v]:
            full |= 1 << v
    spare = [v for v in range(n) if alive[v] and len(adj[v]) < d]
    if not spare:
        return False
    for _ in range(attempts):
        s0 = rng.choice(spare)
        pool = [v for v in spare if color[v] == color[s0] and v != s0]
        S = [s0]
        unc = full & ~reach[s0]
        while unc and len(S) < d and pool:
            bv = _pick(pool, reach, unc, rng)
            if bv < 0:
                break
            S.append(bv)
            unc &= ~reach[bv]
            pool.remove(bv)
        if unc:
            continue
        col = 1 - color[s0]
        if st['free']:
            x = st['free'].pop()
            adj[x] = list(S)
            color[x] = col
            alive[x] = True
        else:
            x = len(adj)
            adj.append(list(S))
            color.append(col)
            alive.append(True)
        for s in S:
            adj[s].append(x)
        st['ext'].append(x)
        return True
    return False


def _valid(st):
    """Exact diameter-4 check of the live graph (distances in live graph only)."""
    adj, alive = st['adj'], st['alive']
    n = len(adj)
    full = 0
    for v in range(n):
        if alive[v]:
            full |= 1 << v
    r = _balls(n, adj, 4)
    return all((r[v] & full) == full for v in range(n) if alive[v])


def _export(st):
    """Compact the live graph to 0..m-1 and return (m, edges)."""
    adj, alive = st['adj'], st['alive']
    ids = [v for v in range(len(adj)) if alive[v]]
    lab = {v: i for i, v in enumerate(ids)}
    edges = []
    for v in ids:
        for w in adj[v]:
            if v < w:
                edges.append((lab[v], lab[w]))
    return len(ids), edges


def _ils(st, d, deadline, rng):
    """Greedy fill, then perturb-and-regrow iterated local search until deadline."""
    while time.monotonic() < deadline and _grow_one(st, d, rng, 25):
        pass
    if not _valid(st):
        return
    cur = len(st['ext'])
    best = _snap(st)
    best_size = cur
    while time.monotonic() < deadline:
        snap = _snap(st)
        k = rng.choice((1, 1, 2, 2, 3))
        for _ in range(min(k, len(st['ext']))):
            _remove(st, rng.choice(st['ext']))
        while time.monotonic() < deadline and _grow_one(st, d, rng, 25):
            pass
        if len(st['ext']) >= cur and _valid(st):
            cur = len(st['ext'])
            if cur > best_size:
                best = _snap(st)
                best_size = cur
        else:
            _restore(st, snap)
    _restore(st, best)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    twin_deadline = t0 + 0.4 * budget
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

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin graph on W(d-2), then perturb-and-regrow extension using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            st = _state(n2, e2)
            _ils(st, d, deadline, rng)
            consider(*_export(st))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
