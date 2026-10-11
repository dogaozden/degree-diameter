import itertools
import random
import time

import lib


class _Abort(Exception):
    """Raised inside the spread search when its node or time budget runs out."""


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
# Spread of W(q): pairwise disjoint lines covering every point.
# Randomized backtracking with minimum-remaining-values branching and restarts.
# A spread gives every point exactly one spare slot for a line-twin.
# ----------------------------------------------------------------------------

def _spread(P, lines, pl, deadline, rng, node_limit=800):
    """Return a list of line indices forming a spread, or None if none is found before deadline."""
    k = len(lines[0]) if lines else 0
    if k == 0 or P % k:
        return None
    target = P // k
    L = len(lines)
    while time.monotonic() < deadline:
        covered = [False] * P
        blocked = [0] * L      # number of covered points on each line
        chosen = []
        nodes = [0]

        def take(l):
            chosen.append(l)
            for p in lines[l]:
                covered[p] = True
                for l2 in pl[p]:
                    blocked[l2] += 1

        def drop():
            l = chosen.pop()
            for p in lines[l]:
                covered[p] = False
                for l2 in pl[p]:
                    blocked[l2] -= 1

        def dfs():
            if len(chosen) == target:
                return True
            nodes[0] += 1
            if nodes[0] > node_limit or time.monotonic() > deadline:
                raise _Abort()
            best = None
            for p in range(P):
                if covered[p]:
                    continue
                cands = [l for l in pl[p] if blocked[l] == 0]
                if not cands:
                    return False
                if best is None or len(cands) < len(best):
                    best = cands
                    if len(best) == 1:
                        break
            if best is None:
                return len(chosen) == target
            rng.shuffle(best)
            for l in best:
                take(l)
                if dfs():
                    return True
                drop()
            return False

        try:
            if dfs():
                return list(chosen)
        except _Abort:
            pass
    return None


# ----------------------------------------------------------------------------
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n          # number of neighbours of v inside S
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
#
# Point twins v_p (p in I, pairwise non-collinear) join the lines through p.
# Line twins w_L (L in J, pairwise disjoint, ideally a spread) join the points of L.
# Every W(q) vertex gains at most one edge, so degree <= q+2.
# ----------------------------------------------------------------------------

def _twin_edges(P, lines, pl, I, J):
    """Return (n, edges) for W(q) plus point twins I and line twins J."""
    L = len(lines)
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

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
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

    # Twin graph on W(d-2): spread for line twins, MIS for point twins.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            q = d - 2
            P, lines = _gq_w(q)
            L = len(lines)
            pl = [[] for _ in range(P)]
            for j, Ls in enumerate(lines):
                for p in Ls:
                    pl[p].append(j)
            padj = [set() for _ in range(P)]      # collinear points
            for Ls in lines:
                for p in Ls:
                    for r in Ls:
                        if p != r:
                            padj[p].add(r)
            ladj = [set() for _ in range(L)]      # lines sharing a point
            for p in range(P):
                for a in pl[p]:
                    for b in pl[p]:
                        if a != b:
                            ladj[a].add(b)

            now = time.monotonic()
            span = max(0.0, deadline - now)
            t_spread = now + 0.3 * span
            J = _spread(P, lines, pl, t_spread, rng)
            if J is None:
                J = _mis(L, [sorted(s) for s in ladj], t_spread + 0.1 * span, rng)

            I = _mis(P, [sorted(s) for s in padj], deadline, rng)

            n2, e2 = _twin_edges(P, lines, pl, I, J)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
