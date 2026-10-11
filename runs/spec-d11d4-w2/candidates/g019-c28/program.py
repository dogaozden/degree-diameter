import itertools
import math
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
    c = [0] * n          # number of neighbours of v inside S
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
            # Restart from the best independent set found so far.
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
    padj = [set() for _ in range(P)]          # collinear points
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]          # lines sharing a point
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
#
# Let R3(v) be the set of vertices within distance 3 of v. A new vertex x on
# side X, joined to a set S of spare-degree vertices on the opposite side Y,
# keeps diameter <= 4 exactly when the union of R3(s) over s in S covers every
# existing vertex. Adding x only shortens distances, so no other pair can break.
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


def _bicolor(n, adj):
    """Return a 2-colouring of every vertex (adj: neighbour sequences)."""
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


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bicolor(n, adj)

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
# Edge-split growth ("swap-grow"), checked move by move with lib.is_valid.
# ----------------------------------------------------------------------------

def _swap_grow(n, edges, d, D, deadline, rng):
    """Grow by edge-split moves until the deadline; return (n, edges), always valid."""
    eset = set()
    for u, v in edges:
        eset.add((u, v) if u < v else (v, u))
    adj = [set() for _ in range(n)]
    for u, v in eset:
        adj[u].add(v)
        adj[v].add(u)
    color = _bicolor(n, adj)

    while time.monotonic() < deadline:
        sat = [v for v in range(n) if len(adj[v]) == d]
        if not sat:
            break
        s = rng.choice(sat)
        t = rng.choice(sorted(adj[s]))
        key = (s, t) if s < t else (t, s)
        eset.discard(key)
        adj[s].discard(t)
        adj[t].discard(s)

        reach = _ball3(n, adj)
        unc = ((1 << n) - 1) & ~reach[s]
        pool = [v for v in range(n) if color[v] == color[s] and v != s and len(adj[v]) < d]
        S = [s]
        while unc and len(S) < d and pool:
            bv = _pick(pool, reach, unc, rng)
            if bv < 0:
                break
            S.append(bv)
            unc &= ~reach[bv]
            pool.remove(bv)

        if unc == 0:
            x = n
            adj.append(set())
            color.append(color[t])
            for w in S:
                adj[w].add(x)
                adj[x].add(w)
                eset.add((w, x))
            if lib.is_valid(n + 1, list(eset), d, D):
                n += 1
                continue
            # Revert the new vertex.
            for w in S:
                adj[w].discard(x)
                eset.discard((w, x))
            adj.pop()
            color.pop()

        # Restore the removed edge.
        adj[s].add(t)
        adj[t].add(s)
        eset.add(key)
    return n, sorted(eset)


# ----------------------------------------------------------------------------
# NEW: bi-Cayley lifts over groups of order G (two orbits, 2G vertices, degree d).
#
# Vertices a_x (x in G) and b_y (y in G); a_x ~ b_{x*s} for s in S, |S| = d.
# Left multiplication is an automorphism, so the graph is vertex-transitive on
# each side. Diameter <= D holds iff the balls of radius D around a_e and b_e
# cover everything. Connection sets are found by hill climbing on the number of
# uncovered vertices, which is cheap to evaluate.
# ----------------------------------------------------------------------------

def _cayley_groups(G):
    """Return (mul, inv) pairs: the cyclic group of order G and some semidirect products Z_m x| Z_k of order G."""
    _, mul, inv = lib.cyclic_group(G)
    groups = [(mul, inv)]
    for k in range(2, min(G, 40) + 1):
        if G % k:
            continue
        m = G // k
        if m < 3:
            continue
        found = 0
        for r in range(2, m):
            if found >= 2:
                break
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                try:
                    _, mul2, inv2 = lib.semidirect_group(m, k, r)
                except ValueError:
                    continue
                groups.append((mul2, inv2))
                found += 1
    return groups


def _cayley_rows(task, s):
    """Return (right-multiplication by s, right-multiplication by s^-1) as lists over the group, cached per task."""
    cache = task["cache"]
    row = cache.get(s)
    if row is None:
        mul, inv, G = task["mul"], task["inv"], task["G"]
        si = inv(s)
        row = ([mul(x, s) for x in range(G)], [mul(y, si) for y in range(G)])
        cache[s] = row
    return row


def _uncovered(G, Rn, Ln, start, D):
    """Count vertices of the bi-Cayley graph not within distance D of vertex `start` (A-vertex 0 or B-vertex 0 = G)."""
    seen = bytearray(2 * G)
    seen[start] = 1
    frontier = [start]
    reached = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < G:
                for col in Rn:
                    w = G + col[v]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                y = v - G
                for col in Ln:
                    w = col[y]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        if not nxt:
            break
        reached += len(nxt)
        frontier = nxt
    return 2 * G - reached


def _cayley_cost(task, S, D):
    """Number of uncovered (vertex, source) pairs for connection set S; zero means diameter <= D."""
    G = task["G"]
    rows = [_cayley_rows(task, s) for s in S]
    Rn = [r[0] for r in rows]
    Ln = [r[1] for r in rows]
    return _uncovered(G, Rn, Ln, 0, D) + _uncovered(G, Rn, Ln, G, D)


def _cayley_step(task, iters, d, D, rng):
    """Run up to `iters` hill-climbing moves; return the connection set once cost reaches 0, else None."""
    G = task["G"]
    for _ in range(iters):
        if task["cost"] == 0:
            return task["S"]
        S = task["S"]
        i = rng.randrange(d)
        t = rng.randrange(G)
        if t in S:
            continue
        S2 = list(S)
        S2[i] = t
        c2 = _cayley_cost(task, S2, D)
        if c2 <= task["cost"] or rng.random() < 0.02:
            task["S"], task["cost"] = S2, c2
    if len(task["cache"]) > 4 * d:
        task["cache"] = {s: _cayley_rows(task, s) for s in task["S"]}
    if task["cost"] == 0:
        return task["S"]
    return None


def _cayley_graph(task, S):
    """Build the bi-Cayley graph (2G vertices; a_x = x, b_y = G + y)."""
    G, mul = task["G"], task["mul"]
    edges = [(x, G + mul(x, s)) for x in range(G) for s in S]
    return 2 * G, edges


def _cayley_phase(d, D, best_n, deadline, rng, consider):
    """Search bi-Cayley lifts of order G > best_n/2 until the deadline; return the final best order."""

    def make_tasks(lo):
        out = []
        for G in range(lo, lo + 4):
            if G < d:
                continue
            for mul, inv in _cayley_groups(G):
                t = {"G": G, "mul": mul, "inv": inv, "cache": {}}
                t["S"] = rng.sample(range(G), d)
                t["cost"] = _cayley_cost(t, t["S"], D)
                out.append(t)
                if time.monotonic() >= deadline:
                    return out
        return out

    tasks = make_tasks(best_n // 2 + 1)
    while time.monotonic() < deadline:
        if not tasks:
            tasks = make_tasks(best_n // 2 + 1)
            if not tasks:
                break
        for t in list(tasks):
            if time.monotonic() >= deadline:
                break
            if 2 * t["G"] <= best_n:
                tasks.remove(t)
                continue
            S = _cayley_step(t, 40, d, D, rng)
            if S is not None:
                tasks.remove(t)
                n2, e2 = _cayley_graph(t, S)
                if consider(n2, e2):
                    best_n = n2
    return best_n


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    end = t0 + budget
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

    # Bold path for D >= 4: part of the time goes to bi-Cayley search.
    bold = D >= 4 and d >= 3
    pspan = (0.55 if bold else 1.0) * budget
    twin_deadline = t0 + 0.4 * pspan
    extend_deadline = t0 + 0.7 * pspan
    parent_deadline = t0 + pspan

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

    # Twin graph on W(d-2), then cover extension, then edge-split growth.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, extend_deadline, rng)
            consider(n3, e3)
            n4, e4 = _swap_grow(n3, e3, d, D, parent_deadline, rng)
            consider(n4, e4)
        except Exception:
            pass

    # New construction: bi-Cayley lifts over groups of order just above half the current best.
    if bold:
        try:
            _cayley_phase(d, D, best[0], end, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
