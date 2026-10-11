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
# Greedy set-cover vertex extension for diameter 4.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _pick(pool, reach, unc, rng):
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob NOISE."""
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


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
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

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            if fails >= MAX_FAILS:
                return n, edges
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
                fails += 1
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Z_m-voltage lifts of small bipartite base graphs (used when D != 4).
# ----------------------------------------------------------------------------

def _base_adj(k, m, perm, volt):
    """Adjacency of the base dart graph: adj[b] = list of (neighbour_base_id * m, voltage mod m)."""
    adj = [[] for _ in range(2 * k)]
    for i in range(len(perm)):
        pi, vi = perm[i], volt[i]
        for u in range(k):
            v = k + pi[u]
            t = vi[u]
            adj[u].append((v * m, t))
            adj[v].append((u * m, (-t) % m))
    return adj


def _lift_score(k, m, adj, D, limit):
    """Total number of (source, vertex) pairs not reached within D steps; stops early once above limit."""
    N = 2 * k * m
    total = 0
    for b0 in range(2 * k):
        seen = bytearray(N)
        s0 = b0 * m
        seen[s0] = 1
        frontier = [s0]
        reached = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                b = x // m
                g = x - b * m
                for bm, t in adj[b]:
                    y = bm + (g + t) % m
                    if not seen[y]:
                        seen[y] = 1
                        nxt.append(y)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += N - reached
        if total > limit:
            return total
    return total


def _lift_edges(k, m, adj):
    """Return (n, edges) for the lift described by the base adjacency."""
    E = set()
    for u in range(k):
        for g in range(m):
            x = u * m + g
            for bm, t in adj[u]:
                y = bm + (g + t) % m
                E.add((x, y))
    return 2 * k * m, sorted(E)


def _lift_search(d, D, k, m, deadline, rng):
    """Hill-climb voltages/matchings for a valid lift on 2*k*m vertices; return (n, edges) or None."""

    def fresh():
        perm = [rng.sample(range(k), k) for _ in range(d)]
        volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
        return perm, volt

    perm, volt = fresh()
    cur = _lift_score(k, m, _base_adj(k, m, perm, volt), D, 1 << 60)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 400:
            perm, volt = fresh()
            cur = _lift_score(k, m, _base_adj(k, m, perm, volt), D, 1 << 60)
            stall = 0
            continue
        i = rng.randrange(d)
        u = rng.randrange(k)
        if rng.random() < 0.6:
            old = volt[i][u]
            volt[i][u] = rng.randrange(m)
            new = _lift_score(k, m, _base_adj(k, m, perm, volt), D, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                volt[i][u] = old
        else:
            u2 = rng.randrange(k)
            if u2 == u:
                continue
            p = perm[i]
            p[u], p[u2] = p[u2], p[u]
            new = _lift_score(k, m, _base_adj(k, m, perm, volt), D, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                p[u], p[u2] = p[u2], p[u]
    return _lift_edges(k, m, _base_adj(k, m, perm, volt))


def _lift_phase(d, D, bn, deadline, rng, consider):
    """Repeatedly search for lifts of growing order above bn until the deadline or the Moore bound."""
    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline and bn < moore:
        ks = [k for k in (2, 3, 4, 5, 6) if 2 * k * (bn // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        m = bn // (2 * k) + 1
        now = time.monotonic()
        slice_end = min(deadline, now + max(4.0, (deadline - now) / 4.0))
        res = _lift_search(d, D, k, m, slice_end, rng)
        if res is not None:
            n, edges = res
            if n > bn and lib.is_valid(n, edges, d, D):
                consider(n, edges)
                bn = n
    return bn


# ----------------------------------------------------------------------------
# NEW: ruin-and-recreate local search on a valid graph.
#
# Each iteration removes 1-3 vertices (preferring vertices added by earlier
# extension steps), which frees their neighbours' degree slots. It then tries to
# re-insert one more vertex than was removed, each new vertex being a set of
# same-colour spare vertices whose radius-(D-1) balls cover every alive vertex.
# The new state is kept only if it is still of diameter <= D and has not
# shrunk; otherwise it is rolled back. Plateau moves are accepted, which lets the
# search drift across equal-order graphs.
# ----------------------------------------------------------------------------

def _balls(adj, r):
    """Per-vertex bitmask of all vertices within distance r (dead vertices with empty adjacency are isolated)."""
    n = len(adj)
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return reach


def _two_color(n, adj):
    """Proper 2-colouring of a bipartite graph by DFS."""
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
    return color


def _extract(adj, alive):
    """Compact the alive vertices to 0..m-1 and return (m, edges)."""
    ids = [v for v in range(len(adj)) if alive[v]]
    idx = {v: i for i, v in enumerate(ids)}
    return len(ids), [(idx[u], idx[v]) for u in ids for v in adj[u] if u < v]


def _ruin_recreate(n0, edges0, d, D, deadline, rng):
    """Ruin-and-recreate search starting from a valid graph; returns the best (n, edges) found."""
    r = D - 1
    adj = [set() for _ in range(n0)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n0, adj)
    alive = [True] * n0
    isext = [False] * n0
    free = []
    n_alive = n0
    best_res = (n0, list(edges0))
    best_n = n0
    moore = lib._moore_bound(d, D)

    while time.monotonic() < deadline and best_n < moore:
        snap = ([set(s) for s in adj], list(alive), list(isext), list(color), list(free), n_alive)
        prev_n = n_alive
        cap = len(adj)

        # Ruin: remove 1-3 alive vertices, preferring extension vertices.
        removed = 0
        for _ in range(rng.choice((1, 1, 2, 2, 3))):
            prefer_ext = rng.random() < 0.7
            x = -1
            for t in range(400):
                y = rng.randrange(cap)
                if alive[y] and (t >= 200 or not prefer_ext or isext[y]):
                    x = y
                    break
            if x < 0:
                break
            for s in adj[x]:
                adj[s].discard(x)
            adj[x] = set()
            alive[x] = False
            isext[x] = False
            free.append(x)
            n_alive -= 1
            removed += 1
        if removed == 0:
            continue

        # Recreate: try to insert removed + 1 vertices by greedy set cover.
        reach = _balls(adj, r)
        full = 0
        for v in range(cap):
            if alive[v]:
                full |= 1 << v
        spare = [v for v in range(cap) if alive[v] and len(adj[v]) < d]
        for _ in range(removed + 1):
            if not spare:
                break
            found = None
            for _t in range(30):
                s0 = rng.choice(spare)
                c0 = color[s0]
                pool = [v for v in spare if v != s0 and color[v] == c0]
                S = [s0]
                unc = full & ~reach[s0]
                while unc and len(S) < d and pool:
                    bg, bv = 0, -1
                    for v in pool:
                        g = (reach[v] & unc).bit_count()
                        if g > bg:
                            bg, bv = g, v
                    if bv < 0:
                        break
                    S.append(bv)
                    unc &= ~reach[bv]
                    pool.remove(bv)
                if not unc:
                    found = (S, c0)
                    break
            if found is None:
                break
            S, c0 = found
            if free:
                y = free.pop()
                alive[y] = True
                isext[y] = True
                color[y] = 1 - c0
                adj[y] = set()
            else:
                y = len(adj)
                adj.append(set())
                alive.append(True)
                isext.append(True)
                color.append(1 - c0)
            for s in S:
                adj[s].add(y)
                adj[y].add(s)
            n_alive += 1
            full |= 1 << y
            reach = _balls(adj, r)
            spare = [v for v in spare if len(adj[v]) < d]

        # Verify: every alive pair within distance D (ball_D(v) = ball_{D-1}(v) + neighbours' balls).
        ok = True
        for v in range(len(adj)):
            if alive[v]:
                x = reach[v]
                for u in adj[v]:
                    x |= reach[u]
                if x & full != full:
                    ok = False
                    break
        if ok and n_alive >= prev_n:
            if n_alive > best_n:
                best_n = n_alive
                best_res = _extract(adj, alive)
        else:
            adj, alive, isext, color, free, n_alive = snap

    return best_res


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    parent_deadline = t0 + 0.5 * budget
    twin_deadline = t0 + 0.35 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)

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

    # Twin graph on W(d-2), then randomized set-cover extension using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Z_m-voltage lifts for the non-D=4 cases (short slice of the budget).
    if D != 4 and D >= 2 and d >= 2:
        try:
            now = time.monotonic()
            lift_end = now + 0.3 * max(0.0, deadline - now)
            _lift_phase(d, D, best[0], lift_end, rng, consider)
        except Exception:
            pass

    # Ruin-and-recreate local search on the best graph found so far.
    if D >= 2 and best[0] < moore and time.monotonic() < deadline:
        try:
            n, edges = _ruin_recreate(best[0], best[1], d, D, deadline, rng)
            consider(n, edges)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
