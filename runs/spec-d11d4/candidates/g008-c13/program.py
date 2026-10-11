import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (pure Python).
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
# Twin construction on W(q), degree q+2 (d = q+2, D = 4).
#
# Point twins for an independent set I of points (pairwise non-collinear),
# line twins for a set J of pairwise disjoint lines. Returns the graph with a
# side label per vertex (0 = point side, 1 = line side).
# ----------------------------------------------------------------------------

def _twin_graph(q, i_deadline, j_deadline, rng):
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

    I = _mis(P, [sorted(s) for s in padj], i_deadline, rng)
    J = _mis(L, [sorted(s) for s in ladj], j_deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    side = [0] * P + [1] * L
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        side.append(0)
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        side.append(1)
        n += 1
    return n, edges, side


# ----------------------------------------------------------------------------
# Greedy augmentation: add new vertices whose neighbourhoods use spare degree.
#
# A new vertex z with neighbour set N is at distance <= D from every vertex
# iff every existing vertex lies within distance D-1 of some u in N. Adding
# z only shrinks distances, so validity is preserved; the final check guards it.
# ----------------------------------------------------------------------------

def _balls_r(n, adj, R):
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _augment(n, edges, side, d, R, deadline, rng):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    edges = list(edges)
    while time.monotonic() < deadline:
        balls = _balls_r(n, adj, R)
        full = (1 << n) - 1
        ok = False
        sides = [0, 1]
        rng.shuffle(sides)
        for s in sides:
            cand = [u for u in range(n) if side[u] != s and deg[u] < d]
            remaining = full
            chosen = []
            while remaining and len(chosen) < d:
                best_u, best_c = -1, 0
                for u in cand:
                    c = (balls[u] & remaining).bit_count()
                    if c > best_c:
                        best_c, best_u = c, u
                if best_c == 0:
                    break
                chosen.append(best_u)
                remaining &= ~balls[best_u]
            if remaining == 0 and chosen:
                z = n
                n += 1
                side.append(s)
                for u in chosen:
                    adj[u].append(z)
                    deg[u] += 1
                    edges.append((u, z))
                adj.append(list(chosen))
                deg.append(len(chosen))
                ok = True
                break
        if not ok:
            break
        if time.monotonic() >= deadline:
            break
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

    if D == 2:
        return best

    # Projective plane incidence graph: degree d, diameter 3.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4:
        # Generalized quadrangle W(d-1): degree d, diameter 4.
        if lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
            try:
                consider(*_gq_incidence(d - 1))
            except Exception:
                pass

        # Twin construction on W(d-2), then greedy augmentation.
        if lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
            try:
                q = d - 2
                n, edges, side = _twin_graph(
                    q,
                    t0 + 0.30 * budget,
                    t0 + 0.55 * budget,
                    rng,
                )
                if lib.is_valid(n, edges, d, D):
                    consider(n, edges)
                    n2, edges2 = _augment(
                        n, list(edges), list(side), d, D - 1,
                        deadline - 1.5, rng,
                    )
                    consider(n2, edges2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
