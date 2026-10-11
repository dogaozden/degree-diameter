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
# Ball bitmasks: reach2[v] = vertices within distance 2, reach3[v] = within 3.
# ----------------------------------------------------------------------------

def _step(reach, adj):
    """One ball-growing round: new[v] = union of reach[u] over u in N[v]."""
    out = []
    for v in range(len(reach)):
        r = reach[v]
        for u in adj[v]:
            r |= reach[u]
        out.append(r)
    return out


def _balls23(n, adj):
    """Return (reach2, reach3) bitmasks of the vertices within distance 2 and 3 of each vertex."""
    reach = [1 << v for v in range(n)]
    reach = _step(reach, adj)
    reach = _step(reach, adj)
    r2 = reach
    r3 = _step(r2, adj)
    return r2, r3


# ----------------------------------------------------------------------------
# Greedy set-cover vertex extension for diameter 4.
#
# Single insertion: a new vertex x joined to a set S of spare vertices on the
# opposite side keeps diameter <= 4 iff the union of R3(s) over s in S covers
# every existing vertex.
#
# Pair insertion (new in this version): two new vertices x, y joined by an edge,
# x attached to S (side cs) and y attached to T (side 1-cs). Every old vertex v
# must satisfy:
#   dist(x, v) <= 4  via  S: v in R3(s) for some s in S,  or via y: v in R2(t), t in T
#   dist(y, v) <= 4  via  T: v in R3(t) for some t in T,  or via x: v in R2(s), s in S
# Both coverage conditions are a two-sided set cover solved greedily. Adding
# vertices and edges never increases a distance, so diameter stays <= 4.
#
# Shortcut edges: when covering fails, add an edge between two spare vertices
# on opposite sides. This also never increases a distance.
# ----------------------------------------------------------------------------

def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Cover all vertices using R3(s0) plus up to d-1 pool vertices; return the chosen set S or None."""
    S = [s0]
    unc = full & ~reach[s0]
    pool = [v for v in pool_all if v != s0]
    while unc and len(S) < d and pool:
        gains = [(reach[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thresh = max(1, int(best * 0.8))
            choices = [i for i, g in enumerate(gains) if g >= thresh]
            i = rng.choice(choices)
        else:
            top = [i for i, g in enumerate(gains) if g == best]
            i = rng.choice(top)
        bv = pool[i]
        S.append(bv)
        unc &= ~reach[bv]
        pool[i] = pool[-1]
        pool.pop()
    if unc:
        return None
    return S


def _pair_attempt(r, b, pool_s, pool_t, r2, r3, full, d, rng):
    """Try to find S (side of r, containing r) and T (side of b, containing b) so that a new
    edge-joined pair x (adjacent to S) and y (adjacent to T) reaches every old vertex within 4.
    Returns (S, T) or None."""
    ux = full & ~(r3[r] | r2[b])
    uy = full & ~(r3[b] | r2[r])
    S = [r]
    T = [b]
    ps = [v for v in pool_s if v != r]
    pt = [v for v in pool_t if v != b]
    rng.shuffle(ps)
    rng.shuffle(pt)
    ps = ps[:250]
    pt = pt[:250]
    while ux or uy:
        gS, iS = 0, -1
        if len(S) < d - 1:
            for i, v in enumerate(ps):
                g = (r3[v] & ux).bit_count() + (r2[v] & uy).bit_count()
                if g > gS:
                    gS, iS = g, i
        gT, iT = 0, -1
        if len(T) < d - 1:
            for i, v in enumerate(pt):
                g = (r3[v] & uy).bit_count() + (r2[v] & ux).bit_count()
                if g > gT:
                    gT, iT = g, i
        if gS <= 0 and gT <= 0:
            break
        if gS >= gT:
            v = ps[iS]
            ps[iS] = ps[-1]
            ps.pop()
            S.append(v)
            ux &= ~r3[v]
            uy &= ~r2[v]
        else:
            v = pt[iT]
            pt[iT] = pt[-1]
            pt.pop()
            T.append(v)
            uy &= ~r3[v]
            ux &= ~r2[v]
    if ux or uy:
        return None
    return S, T


def _insert_pair(n, edges, adj, color, S, T):
    """Insert x (adjacent to S) and y (adjacent to T) with edge x-y; return new vertex count."""
    cs = color[S[0]]
    x, y = n, n + 1
    color.append(1 - cs)   # x
    color.append(cs)       # y
    adj.append([])
    adj.append([])
    for s in S:
        edges.append((s, x))
        adj[s].append(x)
        adj[x].append(s)
    for t in T:
        edges.append((t, y))
        adj[t].append(y)
        adj[y].append(t)
    edges.append((x, y))
    adj[x].append(y)
    adj[y].append(x)
    return n + 2


def _shortcut(edges, adj, color, spare, d, reach, rng):
    """Add one edge between a random spare vertex and the spare opposite-side vertex that gains most coverage."""
    s = rng.choice(spare)
    nb = set(adj[s])
    best, bg = None, -1
    for v in spare:
        if v == s or color[v] == color[s] or v in nb or len(adj[v]) >= d:
            continue
        g = (reach[v] & ~reach[s]).bit_count()
        if g > bg:
            bg, best = g, v
    if best is None:
        return False
    edges.append((s, best))
    adj[s].append(best)
    adj[best].append(s)
    return True


def _extend(n, edges, d, deadline, rng, max_fails):
    """Greedily add vertices (singly or in edge-joined pairs) keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
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

    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        r2, r3 = _balls23(n, adj)
        full = (1 << n) - 1
        s0 = rng.choice(spare)
        cs = color[s0]
        pool_same = [v for v in spare if color[v] == cs]
        pool_opp = [v for v in spare if color[v] != cs]

        # Single-vertex insertion.
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else rng.choice([0.2, 0.35, 0.5])
            S = _cover_attempt(s0, pool_same, r3, full, d, rng, noise)
            if S is not None:
                break
        if S is not None:
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - cs)
            fails = 0
            continue

        # Edge-joined pair insertion.
        done = False
        if pool_opp:
            for attempt in range(2):
                b = rng.choice(pool_opp)
                res = _pair_attempt(s0, b, pool_same, pool_opp, r2, r3, full, d, rng)
                if res is not None:
                    S2, T2 = res
                    n = _insert_pair(n, edges, adj, color, S2, T2)
                    done = True
                    break
        if done:
            fails = 0
            continue

        fails += 1
        # Every other failure, spend spare degree on a diameter-safe shortcut edge.
        if fails % 2 == 0:
            _shortcut(edges, adj, color, spare, d, r3, rng)
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
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
            return True
        return False

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

    # Twin graph on W(d-2) built once, then repeated randomized extensions
    # (single and pair insertions). Runs alternate between restarting from the
    # twin base and continuing from the best extension found so far.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(d - 2, now + 0.35 * (deadline - now), rng)
            consider(*base)
        except Exception:
            base = None

        if base is not None and lib.is_valid(base[0], base[1], d, D):
            ext_best = base
            stagnant = 0
            while time.monotonic() < deadline - 0.5 and stagnant < 6:
                now = time.monotonic()
                remaining = deadline - now
                run_end = min(deadline, now + max(2.0, remaining / 3.0))
                if rng.random() < 0.5:
                    start = ext_best
                else:
                    start = base
                try:
                    n3, e3 = _extend(start[0], start[1], d, run_end, rng, 3000)
                except Exception:
                    stagnant += 1
                    continue
                if n3 > ext_best[0] and lib.is_valid(n3, e3, d, D):
                    ext_best = (n3, e3)
                    consider(n3, e3)
                    stagnant = 0
                else:
                    stagnant += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
