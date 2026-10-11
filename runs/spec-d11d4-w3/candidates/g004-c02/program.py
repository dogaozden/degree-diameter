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
# Shared graph-state helpers.
#
# The working graph is kept as mutable adjacency lists plus a 2-colouring and an
# alive flag per vertex, so vertices can be removed (marked dead) and re-added.
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


def _colors(n, adj):
    """Return a 2-colouring of the graph (assumed bipartite)."""
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


def _grow(adj, color, alive, d, deadline, rng, fail_cap):
    """Greedily append vertices (set-cover extension) keeping diameter <= 4. Returns number added.

    A new vertex x joined to S (same-colour spare vertices, one of which is s0) is safe when the
    union of radius-3 balls of S covers every live vertex. Existing pairs never get longer.
    """
    added = 0
    fails = 0
    while time.monotonic() < deadline and fails < fail_cap:
        n = len(adj)
        reach = _ball3(n, adj)
        full = 0
        for v in range(n):
            if alive[v]:
                full |= 1 << v
        spare = [v for v in range(n) if alive[v] and len(adj[v]) < d]
        if not spare:
            break
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
        for s in S:
            adj[s].append(x)
        adj.append(list(S))
        color.append(1 - color[s0])
        alive.append(True)
        added += 1
        fails = 0
    return added


def _compact(adj, alive):
    """Return (n, edges) of the live part of the graph, relabelled to 0..n-1."""
    edges = [(u, v) for u in range(len(adj)) if alive[u] for v in adj[u] if u < v]
    return lib.relabel(edges)


def _twin_extend(q, d, tw_dl, ex_dl, rng):
    """Twin graph on W(q) followed by greedy set-cover extension. Returns (n, edges)."""
    n2, e2 = _twin_graph(q, tw_dl, rng)
    adj = [[] for _ in range(n2)]
    for u, v in e2:
        adj[u].append(v)
        adj[v].append(u)
    color = _colors(n2, adj)
    alive = [True] * n2
    _grow(adj, color, alive, d, ex_dl, rng, 20000)
    return _compact(adj, alive)


# ----------------------------------------------------------------------------
# NEW: exchange search (remove-one, refill-greedily, plateau acceptance).
#
# Repeatedly pick a random live vertex y, delete it, and try to refill the freed
# degree slots with greedy set-cover extension. A move is kept only if the
# resulting graph still has diameter <= D and the vertex count did not drop.
# Otherwise the snapshot is restored. Accepting net-zero moves gives a plateau
# walk that can escape where pure extension stalls.
# ----------------------------------------------------------------------------

def _exchange(n, edges, d, D, deadline, rng):
    """Improve a valid diameter-D graph by remove-one/refill moves. Returns the best (n, edges) seen."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _colors(n, adj)
    alive = [True] * n
    cur = n
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        live = [v for v in range(len(adj)) if alive[v]]
        if not live:
            break
        y = rng.choice(live)
        s_adj = [list(a) for a in adj]
        s_col = list(color)
        s_alive = list(alive)
        for w in adj[y]:
            adj[w].remove(y)
        adj[y] = []
        alive[y] = False
        added = _grow(adj, color, alive, d, deadline, rng, 150)
        ok = False
        if added >= 1:
            nn, ee = _compact(adj, alive)
            if nn == cur - 1 + added and lib.within_diameter(nn, ee, D):
                ok = True
        if ok:
            cur = nn
            if cur > best_n:
                best_n, best_e = nn, ee
        else:
            adj[:] = s_adj
            color[:] = s_col
            alive[:] = s_alive
    return best_n, best_e


# ----------------------------------------------------------------------------
# Cyclic Haar-graph search: generic fallback for cases with no structured
# construction. Random connection sets S of size d over Z_m, increasing m.
# ----------------------------------------------------------------------------

def _haar_search(d, deadline, D, rng, consider):
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            consider(*found)
            misses = 0
        else:
            misses += 1
        m += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    structured = False

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3 (Moore-optimal).
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            before = best[0]
            consider(*lib.projective_plane_incidence(d - 1))
            if best[0] > before:
                structured = True
        except Exception:
            pass
        if D == 3 and structured:
            return best

    # Twin graph on W(d-2), then greedy set-cover extension. Two attempts share
    # the first half of the budget; the exchange search gets the rest.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        q = d - 2
        twin_end = time.monotonic() + 0.5 * max(0.0, deadline - time.monotonic())
        for attempt in range(2):
            now = time.monotonic()
            rem = twin_end - now
            if rem < 3.0:
                break
            share = rem if attempt == 1 else rem * 0.5
            try:
                n3, e3 = _twin_extend(q, d, now + share * 0.4, now + share, rng)
                before = best[0]
                consider(n3, e3)
                if best[0] > before:
                    structured = True
            except Exception:
                pass

    # Generalized quadrangle W(d-1): degree d, diameter 4 (used if d-1 is a prime power).
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11 and time.monotonic() < deadline:
        try:
            before = best[0]
            consider(*_gq_incidence(d - 1))
            if best[0] > before:
                structured = True
        except Exception:
            pass

    # No structured construction succeeded: spend time on cyclic Haar lifts.
    if not structured and time.monotonic() < deadline:
        _haar_search(d, deadline, D, rng, consider)

    # New: exchange search on the best valid graph found so far, with remaining time.
    if D >= 4 and best[0] > 2 * d and time.monotonic() < deadline - 1.0:
        try:
            en, ee = _exchange(best[0], best[1], d, D, deadline, rng)
            consider(en, ee)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
