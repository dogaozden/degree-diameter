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


def _gq_incidence(P, lines):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set, two solvers:
#   _mis: iterated local search with (1,2)-swaps (from the parent).
#   _kfixed_mis: NEW k-fixed penalty tabu search. It keeps a set S of fixed size
#     k, minimises the number of internal edges of S by swapping vertices under a
#     tabu rule, and grows k whenever the set becomes independent.
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


def _kfixed_mis(n, adj, deadline, rng):
    """k-fixed penalty tabu search for a large independent set (conflicts = edges inside S)."""
    if n == 0:
        return []
    conf = [0] * n          # conf[v] = number of neighbours of v inside S
    inS = [False] * n
    S = []
    tabu_add = [0] * n      # v may not be re-added before this iteration
    tabu_rem = [0] * n      # v may not be removed before this iteration
    best = []
    f = [0]                 # number of edges inside S

    def add(v):
        f[0] += conf[v]
        inS[v] = True
        S.append(v)
        for w in adj[v]:
            conf[w] += 1

    def remove(v):
        inS[v] = False
        S.remove(v)
        for w in adj[v]:
            conf[w] -= 1
        f[0] -= conf[v]

    def pick_add(it, exclude=-1):
        bestc = None
        ties = []
        for v in range(n):
            if inS[v] or v == exclude or tabu_add[v] > it:
                continue
            c = conf[v]
            if bestc is None or c < bestc:
                bestc = c
                ties = [v]
            elif c == bestc:
                ties.append(v)
        if not ties:
            cand = [v for v in range(n) if not inS[v] and v != exclude]
            return rng.choice(cand) if cand else None
        return rng.choice(ties)

    add(rng.randrange(n))
    it = 0
    last_imp = 0
    best_len = 0
    while time.monotonic() < deadline:
        it += 1
        if f[0] == 0:
            if len(S) > best_len:
                best = list(S)
                best_len = len(S)
                last_imp = it
            v = pick_add(it)
            if v is None:
                break
            add(v)
            continue
        if it - last_imp > 30000:
            # Stagnation: restart from a random single vertex.
            for u in list(S):
                remove(u)
            add(rng.randrange(n))
            last_imp = it
            continue
        maxc = -1
        ties = []
        for u in S:
            if tabu_rem[u] > it:
                continue
            c = conf[u]
            if c > maxc:
                maxc = c
                ties = [u]
            elif c == maxc:
                ties.append(u)
        if not ties:
            ties = list(S)
        u = rng.choice(ties)
        remove(u)
        tabu_add[u] = it + 7 + rng.randrange(10)
        v = pick_add(it, exclude=u)
        if v is None:
            add(u)
            continue
        add(v)
        tabu_rem[v] = it + 2 + rng.randrange(4)
    if f[0] == 0 and len(S) > best_len:
        best = list(S)
    return best


def _solve_mis(n, adj, end, rng):
    """Run both solvers on half of the slot each and return the larger independent set."""
    now = time.monotonic()
    mid = now + (end - now) / 2.0
    a = _mis(n, adj, mid, rng)
    b = _kfixed_mis(n, adj, end, rng)
    return a if len(a) >= len(b) else b


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot. We add:
#   * a "point twin" v_p for each p in I (I pairwise non-collinear), adjacent to
#     all lines through p (so each line gets at most one new neighbour);
#   * a "line twin" w_L for each L in J (J pairwise disjoint lines), adjacent to
#     all points of L (so each point gets at most one new neighbour).
# Point-side and line-side resources are independent, so I and J are solved
# separately. The final lib.is_valid check guards against any mistake.
# ----------------------------------------------------------------------------

def _twin_graph(P, lines, deadline, rng):
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
    total = deadline - now
    I = _solve_mis(P, [sorted(s) for s in padj], now + total / 2.0, rng)
    J = _solve_mis(L, [sorted(s) for s in ladj], deadline, rng)

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
            P, lines = _gq_w(d - 1)
            consider(*_gq_incidence(P, lines))
        except Exception:
            pass

    # Twin graph on W(d-2): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            P, lines = _gq_w(d - 2)
            consider(*_twin_graph(P, lines, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
