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
# Randomized greedy set-cover vertex extension for diameter 4.
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

    spare = [v for v in range(n) if len(adj[v]) < d]

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
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
            spare = [v for v in spare if len(adj[v]) < d]
            if len(S) < d:
                spare.append(x)
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# NEW: ruin-and-recreate local search on the extension vertices.
#
# Repeatedly pick a vertex added by the extension phase, delete it (freeing
# its neighbours' degree slots), then try to re-attach up to a few new
# vertices with the same set-cover rule. The move is accepted if the graph is
# still diameter 4 and max degree d with no net loss (or with a tiny chance
# when it loses one vertex, to escape plateaus). Otherwise it is undone
# exactly. Dead vertex ids are recycled, so the universe stays small.
# Base vertices (ids < n0) are never removed, so the twin structure is kept.
# ----------------------------------------------------------------------------

RUIN_TRIES = 25
MAX_ADD = 3
DOWN_ACCEPT = 0.02


def _reach3_dyn(adj, alive):
    """Per-vertex bitmask of alive vertices within distance 3 (dead slots carry no bits)."""
    N = len(adj)
    r = [(1 << v) if alive[v] else 0 for v in range(N)]
    for _ in range(3):
        nr = [0] * N
        for v in range(N):
            if alive[v]:
                acc = r[v]
                for u in adj[v]:
                    acc |= r[u]
                nr[v] = acc
        r = nr
    return r


def _alive_mask(alive):
    m = 0
    for v, a in enumerate(alive):
        if a:
            m |= 1 << v
    return m


def _all_within4(adj, alive):
    """True iff every pair of alive vertices is within distance 4."""
    r = _reach3_dyn(adj, alive)
    am = _alive_mask(alive)
    for v in range(len(adj)):
        if alive[v]:
            acc = r[v]
            for u in adj[v]:
                acc |= r[u]
            if acc & am != am:
                return False
    return True


def _grow_one(adj, alive, color, d, rng, tries):
    """Find a neighbour set S (same colour, spare degree) covering all alive vertices within 3; return (S, colour) or None."""
    r = _reach3_dyn(adj, alive)
    am = _alive_mask(alive)
    spare = [v for v in range(len(adj)) if alive[v] and len(adj[v]) < d]
    if not spare:
        return None
    for _ in range(tries):
        s0 = rng.choice(spare)
        pool = [v for v in spare if color[v] == color[s0] and v != s0]
        S = [s0]
        unc = am & ~r[s0]
        while unc and len(S) < d and pool:
            if rng.random() < NOISE:
                useful = [v for v in pool if r[v] & unc]
                if not useful:
                    break
                bv = rng.choice(useful)
            else:
                bv = max(pool, key=lambda v: (r[v] & unc).bit_count())
                if not (r[bv] & unc):
                    break
            S.append(bv)
            unc &= ~r[bv]
            pool.remove(bv)
        if not unc:
            return S, color[s0]
    return None


def _attach(adj, alive, color, free, S, c):
    """Create a new vertex joined to S (all of colour c) and return its id."""
    if free:
        y = free.pop()
    else:
        y = len(adj)
        adj.append([])
        alive.append(False)
        color.append(-1)
    for s in S:
        adj[s].append(y)
        adj[y].append(s)
    alive[y] = True
    color[y] = 1 - c
    return y


def _ruin_recreate(n0, n, edges, d, deadline, rng):
    """Local search over extension vertices (ids >= n0). Returns (best_n, best_edges)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    alive = [True] * n
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

    free = []
    count = n
    best_n = n
    best_edges = list(edges)

    while time.monotonic() < deadline:
        cands = [v for v in range(n0, len(adj)) if alive[v]]
        if not cands:
            break
        x = rng.choice(cands)
        nb = adj[x]
        for s in nb:
            adj[s].remove(x)
        adj[x] = []
        alive[x] = False

        added = []
        for _ in range(MAX_ADD):
            res = _grow_one(adj, alive, color, d, rng, RUIN_TRIES)
            if res is None:
                break
            S, c = res
            added.append(_attach(adj, alive, color, free, S, c))

        accept = False
        if added:
            accept = _all_within4(adj, alive)
        elif rng.random() < DOWN_ACCEPT:
            accept = _all_within4(adj, alive)

        if accept:
            count += len(added) - 1
            free.append(x)
            if count > best_n:
                best_n = count
                best_edges = [(u, v) for v in range(len(adj)) if alive[v]
                              for u in adj[v] if u > v]
        else:
            for y in reversed(added):
                for s in adj[y]:
                    adj[s].remove(y)
                adj[y] = []
                alive[y] = False
                free.append(y)
            adj[x] = nb
            for s in nb:
                adj[s].append(x)
            alive[x] = True
    return best_n, best_edges


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

    # Twin graph on W(d-2) (degree d), extension, then ruin-and-recreate
    # local search on the extension vertices for the remaining time.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, t0 + 0.2 * budget, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, t0 + 0.45 * budget, rng)
            consider(n3, e3)
            if lib.is_valid(n3, e3, d, D):
                rn, re_ = _ruin_recreate(n2, n3, e3, d, deadline, rng)
                rn2, re2 = lib.relabel(re_)
                consider(rn2, re2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
