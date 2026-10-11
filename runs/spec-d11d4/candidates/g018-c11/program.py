import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as points and totally isotropic lines.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each line as a sorted point list."""
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
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph found before deadline."""
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
# Twin construction on W(q) (degree q+2 for q+1 base degree).
# Point twins: pairwise non-collinear points, each adjacent to lines through it.
# Line twins: pairwise disjoint lines, each adjacent to points on it.
# Returns (n, edges, side) with side 0 = point side, 1 = line side.
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

    side = [0] * P + [1] * L
    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        side.append(0)
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        side.append(1)
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges, side


# ----------------------------------------------------------------------------
# Greedy extension: add new vertices whose neighbours are spare-degree vertices
# on the opposite side and whose radius-(D-1) balls together cover the graph.
# Each addition only shortens distances among old vertices, so the only check
# needed is coverage of the new vertex; the final lib.is_valid guards the rest.
# ----------------------------------------------------------------------------

def _radius_masks(n, adj, r):
    """Bitmask of all vertices within distance r, per vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            m = reach[v]
            for u in adj[v]:
                m |= reach[u]
            new.append(m)
        reach = new
    return reach


def _extend(n, edges, side, d, D, deadline, rng):
    edges = list(edges)
    side = list(side)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    r = D - 1
    while time.monotonic() < deadline:
        reach = _radius_masks(n, adj, r)
        full = (1 << n) - 1
        order = [0, 1]
        rng.shuffle(order)
        placed = False
        for s in order:
            cand = [v for v in range(n) if side[v] != s and len(adj[v]) < d]
            rng.shuffle(cand)
            covered = 0
            chosen = []
            while covered != full and len(chosen) < d:
                bestv, bestg = -1, 0
                for c in cand:
                    g = (reach[c] & ~covered).bit_count()
                    if g > bestg:
                        bestg, bestv = g, c
                if bestv < 0:
                    break
                chosen.append(bestv)
                covered |= reach[bestv]
                cand.remove(bestv)
            if covered == full and chosen:
                x = n
                n += 1
                side.append(s)
                adj.append(list(chosen))
                for b in chosen:
                    adj[b].append(x)
                    edges.append((x, b))
                placed = True
                break
        if not placed:
            break
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, edges):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n

    if D == 2:
        return best

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

    # Base of degree d-1 with spare slots, then twins/extension.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q):
        try:
            if D == 3:
                n0, e0 = lib.projective_plane_incidence(q)
                side0 = [0] * (n0 // 2) + [1] * (n0 // 2)
            elif D >= 4:
                now = time.monotonic()
                mis_deadline = now + 0.55 * (deadline - now)
                n0, e0, side0 = _twin_graph(q, mis_deadline, rng)
            else:
                n0 = 0
            if n0 > 0:
                consider(n0, e0)
                n1, e1 = _extend(n0, e0, side0, d, D, deadline, rng)
                consider(n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
