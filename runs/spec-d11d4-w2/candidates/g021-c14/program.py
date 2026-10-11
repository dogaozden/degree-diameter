"""Twin graph on W(q) with an iterated remove-and-refill local search.

New in this version: an iterated local search (ILS) on the finished
diameter-4 graph. Each step deletes 1-3 previously added vertices, greedily
refills the freed degree with set-cover extensions, and accepts the result
if it is still valid and not smaller. Otherwise the step is undone.
The base construction (generalized quadrangle, MIS twin) is unchanged.
"""
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
# Diameter-4 bookkeeping on a mutable graph state.
#
# State = (adj, color, alive): adj has one list per vertex ever created
# (dead vertices have empty lists), color is the bipartition side, and alive
# is the list of live vertex indices.
# ----------------------------------------------------------------------------

def _balls(adj, alive, rounds):
    """Per-vertex bitmasks of vertices within distance `rounds` (dead vertices ignored)."""
    N = len(adj)
    reach = [0] * N
    for v in alive:
        reach[v] = 1 << v
    for _ in range(rounds):
        new = [0] * N
        for v in alive:
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _diam4_ok(adj, alive):
    """True iff every pair of live vertices is within distance 4."""
    R3 = _balls(adj, alive, 3)
    mask = 0
    for v in alive:
        mask |= 1 << v
    for v in alive:
        r = R3[v]
        for u in adj[v]:
            r |= R3[u]
        if r != mask:
            return False
    return True


def _pick(pool, reach, unc, rng, noise):
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob noise."""
    if rng.random() < noise:
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


def _fill(adj, color, alive, d, rng, deadline, tries):
    """Append set-cover vertices in place while possible; return how many were added.

    A new vertex x on the side opposite s0 joined to S (same side as s0) keeps
    diameter <= 4 exactly when the union of R3(s) over S covers all live vertices.
    R3 is recomputed after every addition so each check is exact.
    """
    added = 0
    while time.monotonic() < deadline:
        R3 = _balls(adj, alive, 3)
        mask = 0
        for v in alive:
            mask |= 1 << v
        spare = [v for v in alive if len(adj[v]) < d]
        if not spare:
            break
        found = None
        for _ in range(tries):
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = mask & ~R3[s0]
            noise = rng.choice((0.0, 0.1, 0.25, 0.4))
            while unc and len(S) < d and pool:
                bv = _pick(pool, R3, unc, rng, noise)
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~R3[bv]
                pool.remove(bv)
            if not unc:
                found = S
                break
        if found is None:
            break
        x = len(adj)
        adj.append(list(found))
        for s in found:
            adj[s].append(x)
        color.append(1 - color[found[0]])
        alive.append(x)
        added += 1
    return added


def _copy_state(adj, color, alive):
    return [list(a) for a in adj], list(color), list(alive)


def _to_graph(adj, alive):
    """Compact live vertices to 0..n-1 and return (n, edges)."""
    idx = {v: i for i, v in enumerate(alive)}
    edges = []
    for v in alive:
        for u in adj[v]:
            if v < u:
                edges.append((idx[v], idx[u]))
    return len(alive), edges


def _ils(n, edges, d, deadline, rng):
    """Grow greedily, then run remove-and-refill iterated local search until deadline.

    Returns the largest valid state found as (n, edges).
    """
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
    alive = list(range(n))
    base_n = n

    _fill(adj, color, alive, d, rng, deadline, tries=30)
    best_cnt = len(alive)
    best_state = _copy_state(adj, color, alive)
    cur_cnt = best_cnt

    while time.monotonic() < deadline:
        snap = _copy_state(adj, color, alive)
        added = [v for v in alive if v >= base_n]
        pool_rm = added if added else alive
        k = min(len(pool_rm), rng.choice((1, 1, 2, 3)))
        for u in rng.sample(pool_rm, k):
            for w in adj[u]:
                adj[w].remove(u)
            adj[u] = []
            alive.remove(u)
        _fill(adj, color, alive, d, rng, deadline, tries=20)
        if len(alive) >= cur_cnt and _diam4_ok(adj, alive):
            cur_cnt = len(alive)
            if cur_cnt > best_cnt:
                best_cnt = cur_cnt
                best_state = _copy_state(adj, color, alive)
        else:
            adj, color, alive = _copy_state(*snap)

    return _to_graph(best_state[0], best_state[2])


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

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3.
    if D == 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D < 4:
        if not lib.is_valid(best[0], best[1], d, D):
            return 2, [(0, 1)]
        return best

    # Starting graph for diameter 4: twin graph on W(d-2) (degree d) if possible,
    # otherwise the generalized quadrangle incidence graph W(d-1).
    start = None
    if lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        q = d - 2
        try:
            now = time.monotonic()
            start = _twin_graph(q, now + 0.4 * (deadline - now), rng)
            consider(*start)
        except Exception:
            start = None
    if start is None and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            start = _gq_incidence(d - 1)
            consider(*start)
        except Exception:
            start = None

    if start is not None:
        try:
            n2, e2 = _ils(start[0], start[1], d, deadline, rng)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
