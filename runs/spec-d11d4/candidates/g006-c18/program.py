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
# Dominating-set packing on the line graph of W(q).
#
# A "point twin" attached to a set T of lines is safe (distance <= 4 to every
# original vertex and twin) when T dominates the lines: every line is in T or
# meets a line of T. Point twins need spare degree on lines (spare = 1 for
# W(d-2) with degree d), so each line may belong to at most one class.
# Classes must have size <= d. Greedy randomized cover builds such classes.
# ----------------------------------------------------------------------------

def _greedy_class(L, nbr, used, d, rng):
    """Try to find one dominating set (size <= d) using only unused lines; return list or None."""
    gain = [len(nb) for nb in nbr]
    covered = [False] * L
    remaining = L
    chosen = []
    inchosen = [False] * L
    while remaining and len(chosen) < d:
        best = -1
        bestkey = None
        for c in range(L):
            if used[c] or inchosen[c]:
                continue
            g = gain[c]
            if g <= 0:
                continue
            key = (g, rng.random())
            if bestkey is None or key > bestkey:
                bestkey = key
                best = c
        if best < 0:
            break
        chosen.append(best)
        inchosen[best] = True
        for x in nbr[best]:
            if not covered[x]:
                covered[x] = True
                remaining -= 1
                for y in nbr[x]:
                    gain[y] -= 1
    return chosen if remaining == 0 else None


def _dom_classes(L, nbr, d, deadline, rng, tries=8):
    """Pack disjoint dominating line-sets of size <= d; nbr[c] is the closed neighbourhood of line c."""
    used = [False] * L
    classes = []
    while time.monotonic() < deadline:
        found = None
        for _ in range(tries):
            if time.monotonic() >= deadline:
                break
            found = _greedy_class(L, nbr, used, d, rng)
            if found is not None:
                break
        if found is None:
            break
        for c in found:
            used[c] = True
        classes.append(found)
    return classes


def _twin_v2(q, d, deadline, rng, consider):
    """W(q) (degree q+1, spare 1 per vertex) plus line twins (spread) and point twins (star or dominating classes)."""
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

    base = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]

    now = time.monotonic()
    span = max(0.0, deadline - now)

    # Line twins: pairwise disjoint lines (a partial spread).
    J = _mis(L, [sorted(s) for s in ladj], now + 0.45 * span, rng)

    # Point twins, variant A: dominating classes of lines with size <= d.
    nbr = [sorted(ladj[j] | {j}) for j in range(L)]
    classes = _dom_classes(L, nbr, d, now + 0.6 * span, rng)

    # Point twins, variant B: pairwise non-collinear points (stars of lines).
    I = _mis(P, [sorted(s) for s in padj], now + 0.95 * span, rng)

    def assemble(point_twin_nbrs):
        n = P + L
        edges = list(base)
        for js in J:
            for p in lines[js]:
                edges.append((p, n))
            n += 1
        for nb in point_twin_nbrs:
            for j in nb:
                edges.append((P + j, n))
            n += 1
        return n, edges

    consider(*assemble([pl[p] for p in I]))
    if classes:
        consider(*assemble(classes))


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

    # W(d-2) with line twins and point twins (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            _twin_v2(d - 2, d, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
